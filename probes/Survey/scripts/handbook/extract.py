# -*- coding: utf-8 -*-
# 对话记录的增量提取: 把主会话与子智能体的 JSONL 记录压成小的分类摘录, 供 digest.py 与人工蒸馏手册 (Survey/EBOHandbook.md).
#
# 用法 (任意目录):
#   python3 probes/Survey/scripts/handbook/extract.py --root <项目记录目录> --out <摘录目录> [--tasks <后台任务目录> ...]
#   python3 probes/Survey/scripts/handbook/extract.py ... --dry-run     # 只列出要处理的文件, 不写状态
#   python3 probes/Survey/scripts/handbook/extract.py ... --reset       # 忘掉状态, 从头处理 (摘录目录要先清空, 否则会重复)
#   python3 probes/Survey/scripts/handbook/extract.py ... --session <会话 id>   # 只处理这个会话 (可重复)
#
# <项目记录目录> 是 Claude Code 存本仓库对话的目录 (形如 ~/.claude/projects/<仓库路径改写>), 其下:
#   <会话>.jsonl                       主会话
#   <会话>/subagents/agent-<id>.jsonl  子智能体 (旁边的 .meta.json 有简述与模型)
# <后台任务目录> 形如 <系统临时目录>/claude-<uid>/<仓库路径改写>/<会话>/tasks, 其中 b*.output 是后台命令的输出;
#   指向 subagents 的符号链接跳过 (已由 --root 处理).
#
# 增量: 状态文件 (默认与本脚本同目录的 state.json, 进仓库) 按 "相对 --root 的路径" 记每个文件已处理到的字节位置.
#   文件变长 (主会话还在写) 只处理新增的完整行; 文件变短视为重写, 从头处理. 状态里不存绝对路径.
#   待配对的工具调用 (tool_use 还没等到 tool_result) 存在状态里, 下次接着配对.
# 摘录 (JSONL, 每类一个文件) 一律追加写进 --out; --out 应放在仓库外 (摘录含作者原话与机器路径的痕迹, 虽已做脱敏).
#
# 脱敏: 家目录, 系统临时目录, 邮箱, 形如令牌的串, .local 主机名, 在写出前替换成 <home>, <tmp>, <email>, <token>, <host>.
#
# 输出的分类 (--out 下的文件名):
#   human.jsonl        主会话里作者亲手发的消息 (不含工具结果, 系统注入, 钩子)
#   compact.jsonl      会话压缩时的摘要 (含更早会话的经过)
#   coord_text.jsonl   主会话助手的正文 (汇报)
#   ask.jsonl          AskUserQuestion 的问题, 选项与作者的回答
#   dispatch.jsonl     Agent 派发 (简述, 模型, 类型, 简报) 与 SendMessage (续派, 转告)
#   errors.jsonl       Bash/Monitor 结果里的错误: Agda 错误类 (agda:TerminationIssue 等, 取自 "error: [..]"), 堆耗尽 (含当时的堆上限 MB),
#                      退出码 251 / 124 / 非 0, 超时, K 相关
#   agda_runs.jsonl    含 agda 的命令: 堆上限 (+RTS -M), 文件, 退出码, 用时 (能读到的话), 是否堆耗尽
#   corrections.jsonl  更正类语句 (更正, 纠正, 不对, 其实, 推翻, 撤回, 改口, 搞错, 说错, 误判)
#   sub_brief.jsonl    子智能体的简报 (第一条用户消息) 与 meta
#   sub_report.jsonl   子智能体的最终报告 (SubagentHandback; 没有则记最后一条正文为 kind=lasttext)
#   task_out.jsonl     后台任务输出 (小文件, 截断)
import argparse, glob, io, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_STATE = os.path.join(HERE, 'state.json')

CAP = dict(human=6000, compact=40000, coord=8000, prompt=10000, msg=4000, report=16000,
           cmd=900, snip=700, task=3000, corr=500)

# ---------- 脱敏 ----------
SAN = [
    (re.compile(r'/private/tmp/claude-\d+/[^\s\'"`)]*?/scratchpad'), '<scratch>'),
    (re.compile(r'/private/tmp/claude-\d+/[^\s\'"`)]+'), '<tmp>'),
    (re.compile(r'/(?:private/)?tmp/claude-\d+'), '<tmp>'),
    (re.compile(r'/Users/[^/\s\'"`]+/Agentic/agda-googology'), '<repo>'),
    (re.compile(r'/Users/[^/\s\'"`]+'), '<home>'),
    (re.compile(r'/home/[^/\s\'"`]+'), '<home>'),
    (re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'), '<email>'),
    (re.compile(r'\b(?:sk-[A-Za-z0-9_-]{16,}|gh[pousr]_[A-Za-z0-9]{20,}|xox[abp]-[A-Za-z0-9-]{10,})'), '<token>'),
    (re.compile(r'\b[A-Za-z0-9-]+\.local\b'), '<host>'),
]

def san(s):
    if not isinstance(s, str):
        s = json.dumps(s, ensure_ascii=False)
    for r, t in SAN:
        s = r.sub(t, s)
    return s

def cap(s, n):
    s = san(s)
    return s if len(s) <= n else s[:n] + ' …[截断 %d 字]' % (len(s) - n)

# ---------- 识别 ----------
# Agda 2.8 的报错形如 "<文件>:<行>.<列>-...: error: [TerminationIssue]"; 直接取方括号里的错误类.
AGDA_ERR = re.compile(r'error: \[([\w.]+)\]')
HEAPMB = re.compile(r'Current maximum heap size is \d+ bytes \((\d+) MB\)')
ERR = [
    ('heap', re.compile(r'Heap exhausted|heap overflow|Killed: 9')),
    ('exit251', re.compile(r'(?:Exit code|exit[= :]+|退出码[ =:]*)251\b')),
    ('timeout', re.compile(r'Command timed out|timed out after|(?:Exit code|exit[= :]+)124\b|Terminated: 15')),
    ('noK', re.compile(r'K has been disabled|because K is disabled')),
    ('exitnz', re.compile(r'(?:Exit code|exit[= :]+|退出码[ =:]*)([1-9]\d*)\b')),
]
CORR = re.compile(r'更正|纠正|不对|其实|推翻|撤回|改口|搞错|说错|误判|弄错|收回')
AGDA = re.compile(r'(?<![\w/.-])agda(?:\s|$)')
RTS = re.compile(r'-M\s*(\d+(?:\.\d+)?)\s*([GgMm])')
FILE = re.compile(r'([\w/.-]+\.lagda\.md|[\w/.-]+\.agda)\b')
EXIT = re.compile(r'(?:Exit code|exit(?:code)?[= :]+|退出码[ =:]*|EXIT[= :]+|rc[= :]+)(-?\d+)', re.I)
DUR = re.compile(r'(?:real|elapsed|用时|耗时)[ \t:=]*([\d.:]+\s*(?:s|m|min|秒|分钟)?)|(\d+(?:\.\d+)?)s\b')

def text_of(content):
    if isinstance(content, str):
        return content
    out = []
    for x in content or []:
        if isinstance(x, dict):
            if x.get('type') == 'text':
                out.append(x.get('text', ''))
            elif x.get('type') == 'tool_result':
                out.append(text_of(x.get('content')))
    return '\n'.join(out)

def is_human(d, txt):
    if d.get('isMeta') or d.get('isCompactSummary'):
        return False
    o = d.get('origin')
    if isinstance(o, dict) and o.get('kind') not in (None, 'human'):
        return False
    ps = d.get('promptSource')
    if ps is None and not (isinstance(o, dict) and o.get('kind') == 'human'):
        # 旧版记录没有这两个字段: 用内容排除系统注入
        if re.match(r'\s*<(?:system-reminder|local-command|command-|task-notification|user-prompt-submit-hook)', txt):
            return False
        if txt.startswith('[Request interrupted') or txt.startswith('Caveat:'):
            return False
    return bool(txt.strip())

def snippet(s, m, w):
    a = max(0, m.start() - w // 2)
    return s[a:m.end() + w // 2]

# ---------- 主流程 ----------
class Out:
    def __init__(self, d, dry):
        self.d, self.dry, self.fs, self.n = d, dry, {}, {}
    def w(self, cat, rec):
        self.n[cat] = self.n.get(cat, 0) + 1
        if self.dry:
            return
        if cat not in self.fs:
            self.fs[cat] = io.open(os.path.join(self.d, cat + '.jsonl'), 'a', encoding='utf-8')
        self.fs[cat].write(json.dumps(rec, ensure_ascii=False) + '\n')
    def close(self):
        for f in self.fs.values():
            f.close()

def process(path, key, kind, st, out, meta):
    size = os.path.getsize(path)
    ent = st.get(key, {})
    off = ent.get('offset', 0)
    if size < off:
        off, ent = 0, {}
    if size == off:
        return False
    pending = ent.get('pending', {})
    first_user_seen = ent.get('first_user_seen', False)
    last_text = None
    agent = os.path.basename(path)[len('agent-'):-len('.jsonl')] if kind == 'sub' else None
    base = dict(src=key, kind=kind)
    if agent:
        base['agent'] = agent
    with io.open(path, 'rb') as f:
        f.seek(off)
        pos = off
        for raw in f:
            if not raw.endswith(b'\n'):
                break  # 未写完的行, 下次再读
            pos += len(raw)
            try:
                d = json.loads(raw.decode('utf-8', 'replace'))
            except ValueError:
                continue
            t = d.get('type')
            ts = d.get('timestamp', '')
            if t == 'user':
                m = d.get('message', {}) or {}
                ct = m.get('content')
                # 工具结果
                if isinstance(ct, list):
                    for x in ct:
                        if isinstance(x, dict) and x.get('type') == 'tool_result':
                            handle_result(x, pending, out, base, ts)
                txt = ct if isinstance(ct, str) else '\n'.join(
                    x.get('text', '') for x in (ct or []) if isinstance(x, dict) and x.get('type') == 'text')
                if not txt:
                    continue
                if d.get('isCompactSummary'):
                    out.w('compact', dict(base, ts=ts, text=cap(txt, CAP['compact'])))
                    continue
                if kind == 'sub' and not first_user_seen:
                    first_user_seen = True
                    out.w('sub_brief', dict(base, ts=ts, meta=meta, text=cap(txt, CAP['prompt'])))
                    continue
                if kind == 'main' and is_human(d, txt):
                    out.w('human', dict(base, ts=ts, source=d.get('promptSource'), text=cap(txt, CAP['human'])))
                    for mm in CORR.finditer(txt):
                        out.w('corrections', dict(base, ts=ts, who='author', text=cap(snippet(txt, mm, CAP['corr']), CAP['corr'] + 50)))
                        break
            elif t == 'assistant':
                for x in (d.get('message', {}) or {}).get('content', []) or []:
                    if not isinstance(x, dict):
                        continue
                    if x.get('type') == 'text' and x.get('text', '').strip():
                        tx = x['text']
                        last_text = (ts, tx)
                        if kind == 'main':
                            out.w('coord_text', dict(base, ts=ts, text=cap(tx, CAP['coord'])))
                        seen = set()
                        for mm in CORR.finditer(tx):
                            if mm.group(0) in seen:
                                continue
                            seen.add(mm.group(0))
                            out.w('corrections', dict(base, ts=ts, who='assistant', word=mm.group(0),
                                                      text=cap(snippet(tx, mm, CAP['corr']), CAP['corr'] + 50)))
                    elif x.get('type') == 'tool_use':
                        handle_use(x, pending, out, base, ts)
    # 收尾
    if kind == 'sub' and last_text is not None:
        out.w('sub_report', dict(base, ts=last_text[0], kind2='lasttext', meta=meta, text=cap(last_text[1], CAP['report'])))
    if len(pending) > 300:
        pending = dict(list(pending.items())[-300:])
    st[key] = dict(offset=pos, size=size, pending=pending, first_user_seen=first_user_seen)
    return True

def handle_use(x, pending, out, base, ts):
    name, inp, uid = x.get('name'), x.get('input', {}) or {}, x.get('id')
    if name == 'AskUserQuestion':
        pending[uid] = dict(name=name, ts=ts, q=cap(inp, CAP['prompt']))
    elif name == 'Agent':
        rec = dict(base, ts=ts, tool='Agent', description=san(inp.get('description', '')),
                   model=inp.get('model'), subagent_type=inp.get('subagent_type'),
                   background=inp.get('run_in_background'), prompt=cap(inp.get('prompt', ''), CAP['prompt']))
        out.w('dispatch', rec)
        pending[uid] = dict(name=name, ts=ts, d=rec['description'])
    elif name == 'SendMessage':
        out.w('dispatch', dict(base, ts=ts, tool='SendMessage', to=san(inp.get('to', inp.get('recipient', ''))),
                               message=cap(inp.get('message', inp.get('content', '')), CAP['msg'])))
    elif name == 'SubagentHandback':
        out.w('sub_report', dict(base, ts=ts, kind2='handback', text=cap(inp.get('message', ''), CAP['report'])))
    elif name == 'Bash':
        cmd = inp.get('command', '')
        pending[uid] = dict(name=name, ts=ts, cmd=cap(cmd, CAP['cmd']), agda=bool(AGDA.search(cmd)),
                            bg=bool(inp.get('run_in_background')))
    elif name in ('Monitor', 'TaskStop', 'Write', 'Edit', 'Read'):
        pending[uid] = dict(name=name, ts=ts, cmd=cap(inp.get('file_path', inp.get('command', inp)), 300))

def handle_result(x, pending, out, base, ts):
    uid = x.get('tool_use_id')
    p = pending.pop(uid, None)
    body = text_of(x.get('content'))
    is_err = bool(x.get('is_error'))
    if p is None:
        p = dict(name='?', cmd='')
    nm = p.get('name')
    if nm == 'AskUserQuestion':
        out.w('ask', dict(base, ts=p.get('ts'), question=p.get('q'), answer=cap(body, CAP['msg'])))
        return
    if nm == 'Agent':
        m = re.search(r'agentId:\s*([0-9a-f]+)', body)
        out.w('dispatch', dict(base, ts=ts, tool='AgentResult', description=p.get('d'),
                               agent=m.group(1) if m else None, result=cap(body, 1500)))
        return
    cmd = p.get('cmd', '')
    if nm == 'Bash' and p.get('agda'):
        mm = RTS.search(cmd)
        ex = EXIT.findall(body)
        out.w('agda_runs', dict(base, ts=ts, cmd=cmd, heap=(mm.group(1) + mm.group(2).upper()) if mm else None,
                                files=sorted(set(os.path.basename(f) for f in FILE.findall(cmd)))[:12],
                                exits=ex[-6:], is_error=is_err, bg=p.get('bg'),
                                heap_exhausted=bool(ERR[0][1].search(body)), agda_errs=sorted(set(AGDA_ERR.findall(body)))[:8],
                                dur=[a or b for a, b in DUR.findall(body)][-4:],
                                tail=cap(body[-600:], 700)))
    if nm not in ('Bash', 'Monitor', '?') and not is_err:
        return  # Read/Write 等的结果是文件内容, 不当报错
    codes = AGDA_ERR.findall(body)
    hits = [(tag, r.search(body)) for tag, r in ERR]
    hits = [(t, m) for t, m in hits if m]
    if is_err and not hits and not codes:
        hits.append(('is_error', None))
    if hits or codes:
        tags = sorted(set(['agda:' + c for c in codes])) + [h[0] for h in hits]
        m = AGDA_ERR.search(body) or next((h[1] for h in hits if h[1] is not None), None)
        hm = HEAPMB.search(body)
        out.w('errors', dict(base, ts=ts, tool=nm, tags=tags, cmd=cmd, heap_mb=int(hm.group(1)) if hm else None,
                             snippet=cap(snippet(body, m, CAP['snip']) if m else body[:CAP['snip']], CAP['snip'] + 50)))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--tasks', action='append', default=[])
    ap.add_argument('--state', default=DEFAULT_STATE)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--reset', action='store_true')
    ap.add_argument('--session', action='append', default=[],
                    help='只处理这些会话 (会话 id, 可重复); 默认全部')
    a = ap.parse_args()
    root = os.path.abspath(os.path.expanduser(a.root))
    os.makedirs(a.out, exist_ok=True)
    st = {}
    if os.path.exists(a.state) and not a.reset:
        with io.open(a.state, encoding='utf-8') as f:
            st = json.load(f)
    files = st.setdefault('files', {})
    out = Out(a.out, a.dry_run)
    done = 0
    todo = []
    for p in sorted(glob.glob(os.path.join(root, '*.jsonl'))):
        todo.append((p, os.path.relpath(p, root), 'main', None))
    for p in sorted(glob.glob(os.path.join(root, '*', 'subagents', '*.jsonl'))):
        mp = p[:-len('.jsonl')] + '.meta.json'
        meta = None
        if os.path.exists(mp):
            try:
                with io.open(mp, encoding='utf-8') as f:
                    mj = json.load(f)
                meta = {k: mj.get(k) for k in ('description', 'model', 'agentType', 'requestShape', 'spawnDepth')}
                meta['description'] = san(meta.get('description') or '')
            except ValueError:
                pass
        todo.append((p, os.path.relpath(p, root), 'sub', meta))
    if a.session:
        todo = [t for t in todo if t[1].split(os.sep)[0].replace('.jsonl', '') in a.session]
    for p, key, kind, meta in todo:
        ent = files.get(key, {})
        if os.path.getsize(p) == ent.get('offset', -1):
            continue
        if a.dry_run:
            print('处理', key, os.path.getsize(p) - ent.get('offset', 0), '字节')
            continue
        if process(p, key, kind, files, out, meta):
            done += 1
    for tdir in a.tasks:
        tdir = os.path.abspath(os.path.expanduser(tdir))
        sess = os.path.basename(os.path.dirname(tdir))
        for p in sorted(glob.glob(os.path.join(tdir, '*.output'))):
            if os.path.islink(p):
                continue
            key = 'tasks/%s/%s' % (sess, os.path.basename(p))
            sz = os.path.getsize(p)
            if files.get(key, {}).get('size') == sz:
                continue
            if a.dry_run:
                print('处理', key, sz, '字节')
                continue
            with io.open(p, encoding='utf-8', errors='replace') as f:
                body = f.read(200000)
            out.w('task_out', dict(src=key, kind='task', ts=os.path.getmtime(p), text=cap(body[:CAP['task']], CAP['task'])))
            codes = AGDA_ERR.findall(body)
            hits = [(t, r.search(body)) for t, r in ERR]
            hits = [(t, m) for t, m in hits if m]
            if codes or hits:
                m = AGDA_ERR.search(body) or hits[0][1]
                out.w('errors', dict(src=key, kind='task', ts=os.path.getmtime(p), tool='bg', cmd='',
                                     tags=sorted(set('agda:' + c for c in codes)) + [t for t, _ in hits],
                                     snippet=cap(snippet(body, m, CAP['snip']), CAP['snip'] + 50)))
            files[key] = dict(size=sz)
            done += 1
    out.close()
    if not a.dry_run:
        with io.open(a.state + '.tmp', 'w', encoding='utf-8') as f:
            json.dump(st, f, ensure_ascii=False, indent=0, sort_keys=True)
        os.replace(a.state + '.tmp', a.state)
    print('新处理文件 %d; 摘录条数 %s' % (done, json.dumps(out.n, ensure_ascii=False)))

if __name__ == '__main__':
    main()
