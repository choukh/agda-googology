# -*- coding: utf-8 -*-
# 把一路子智能体的简报、中途消息、回报原文与运行数字从它的转录里取出来，写成一份留档。
#
# 用法 (仓库根目录):
#   python3 probes/Survey/scripts/agentreport.py --transcript <转录.jsonl> --out <留档.md> \
#       --title "<路名>" [--prefix "<文件前缀>"] [--dir "<文件所在目录, 默认 probes/OCF/Align/>"] \
#       [--log "<LOG 里复核那一节的标题>"] \
#       [--verdict "<主审复核后的一句结论>"] [--pending]
#
# 转录是 Claude Code 存的子智能体记录 (会话目录下 subagents/agent-<id>.jsonl)，在仓库之外；路径由调用者给。
# --pending: 这一路还在跑。只取简报，不读它的任何输出。
#
# 写出的内容: 简报与回报是原文，只做两处机械改动并在文首写明:
#   (1) 本机路径换成 <仓库>、<实验目录>、<临时目录>、<主目录> (仓库文件里不写本机路径);
#   (2) 原文里的标题降两级，免得打乱留档自己的层次。
# 数字的口径: token 取转录里每条模型消息的 usage 字段，按消息去重后相加；
#   agda 次数是命令里同时含 "agda " 与 "+RTS" 的 Bash 调用数，是粗数。
import argparse, json, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
HOME = os.path.expanduser('~')


def blocks(content):
    if isinstance(content, str):
        return [dict(type='text', text=content)]
    return [c for c in (content or []) if isinstance(c, dict)]


def read(path, pending):
    r = dict(brief='', coord=[], handbacks=[], usage={}, models=set(), efforts=set(), tools=0,
             agda=0, written=set(), first='', last='', scratch='')
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            try:
                o = json.loads(line)
            except Exception:
                continue
            t, ts = o.get('type'), o.get('timestamp', '')
            if t == 'attachment':
                a = o.get('attachment') or {}
                if a.get('type') == 'environment':
                    r['scratch'] = (a.get('snapshot') or {}).get('scratchpadDirectory', '')
                if pending:
                    continue
                if a.get('type') == 'queued_command' and (a.get('origin') or {}).get('kind') == 'coordinator':
                    r['coord'].append((ts, a.get('prompt', '')))
                continue
            if t == 'user':
                c = (o.get('message') or {}).get('content')
                if not r['brief'] and isinstance(c, str):
                    r['brief'] = c
                    r['first'] = ts
                    if pending and r['scratch']:
                        break
                elif not pending:
                    # 续派 (SendMessage 给已结束的一路) 的消息在转录里是一条 user 消息, 带这句前缀.
                    tx = c if isinstance(c, str) else ''.join(b.get('text', '') for b in blocks(c) if b.get('type') == 'text')
                    pre = 'The coordinator sent a message while you were working:'
                    if tx.startswith(pre):
                        r['coord'].append((ts, tx[len(pre):].lstrip('\n')))
                continue
            if pending:
                continue
            if t == 'api-request':
                m = re.search(r'"effort":"([a-z]+)"', line)
                if m:
                    r['efforts'].add(m.group(1))
                continue
            if t != 'assistant':
                continue
            if ts:
                r['last'] = ts
            msg = o.get('message') or {}
            if msg.get('model'):
                r['models'].add(msg['model'])
            if msg.get('id') and msg.get('usage'):
                r['usage'][msg['id']] = msg['usage']
            for b in blocks(msg.get('content')):
                if b.get('type') != 'tool_use':
                    continue
                r['tools'] += 1
                inp = b.get('input') or {}
                if b.get('name') == 'SubagentHandback':
                    r['handbacks'].append((ts, inp.get('message', '')))
                if b.get('name') == 'Write' and isinstance(inp.get('file_path'), str):
                    r['written'].add(inp['file_path'])
                cmd = inp.get('command', '')
                if isinstance(cmd, str) and 'agda ' in cmd and '+RTS' in cmd:
                    r['agda'] += 1
    return r


def clean(text, scratch):
    if scratch:
        text = text.replace(scratch, '<实验目录>')
    text = text.replace(ROOT, '<仓库>')
    text = re.sub(r'/private/tmp/claude-[^\s`"\')]*', '<临时目录>', text)
    text = re.sub(r'/tmp/claude-[^\s`"\')]*', '<临时目录>', text)
    text = text.replace(HOME, '<主目录>')
    return text


def demote(text):
    out, fence = [], False
    for ln in text.split('\n'):
        if ln.lstrip().startswith('```') or ln.lstrip().startswith('~~~'):
            fence = not fence
        if not fence and re.match(r'#{1,4} ', ln):
            ln = '##' + ln
        out.append(ln)
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--transcript', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--title', required=True)
    ap.add_argument('--prefix', default='')
    ap.add_argument('--dir', default='probes/OCF/Align/')
    ap.add_argument('--log', default='')
    ap.add_argument('--verdict', default='')
    ap.add_argument('--pending', action='store_true')
    a = ap.parse_args()
    r = read(a.transcript, a.pending)
    sc = r['scratch']
    L = ['# ' + a.title + '：简报与回报原文（留档）', '']
    L += ['> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。',
          '> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。', '']
    L += ['| 项 | 值 |', '|---|---|']
    if a.pending:
        L += ['| 状态 | 在跑，尚未返回；本文件只有简报，返回并复核后补全 |',
              '| 派出 (转录的时间戳，UTC) | %s |' % r['first'][:16].replace('T', ' ')]
    else:
        tot = dict(o=0, cc=0, cr=0, i=0)
        for u in r['usage'].values():
            tot['o'] += u.get('output_tokens', 0) or 0
            tot['cc'] += u.get('cache_creation_input_tokens', 0) or 0
            tot['cr'] += u.get('cache_read_input_tokens', 0) or 0
            tot['i'] += u.get('input_tokens', 0) or 0
        L += ['| 模型 | %s |' % ', '.join(sorted(r['models'])),
              '| effort (转录里请求的字段) | %s |' % (', '.join(sorted(r['efforts'])) or '未记录'),
              '| 起止 (转录的时间戳，UTC) | %s 至 %s |' % (r['first'][:16].replace('T', ' '), r['last'][11:16]),
              '| 工具调用 / agda 编译 (粗数) | %d / %d |' % (r['tools'], r['agda']),
              '| token (usage 字段，按消息去重) | 输出 %d；新写入缓存的输入 %d；读缓存的输入 %d；其余输入 %d |' % (tot['o'], tot['cc'], tot['cr'], tot['i'])]
        w = sorted(os.path.basename(p) for p in r['written'] if p.startswith(os.path.join(ROOT, 'probes') + os.sep))
        L += ['| 写过的仓库文件 | %s |' % (', '.join('`%s`' % x for x in w) or '无')]
    if a.prefix:
        L += ['| 文件前缀 | `%s` (在 `%s`) |' % (a.prefix, a.dir)]
    if a.log:
        L += ['| 主审的复核记录 | `probes/LOG.md` 的 “%s” 一节 |' % a.log]
    if a.verdict:
        L += ['| 主审复核后的一句结论 | %s |' % a.verdict]
    L += ['', '## 简报原文', '', demote(clean(r['brief'], sc)).rstrip(), '']
    if not a.pending:
        if r['coord']:
            L += ['## 中途消息（主审发给这一路）', '']
            for ts, tx in r['coord']:
                L += ['转录时间戳 %s (UTC)：' % ts[:16].replace('T', ' '), '', demote(clean(tx, sc)).rstrip(), '']
        L += ['## 回报原文', '']
        if not r['handbacks']:
            L += ['转录里没有找到回报。', '']
        for k, (ts, tx) in enumerate(r['handbacks']):
            if len(r['handbacks']) > 1:
                L += ['第 %d 份，转录时间戳 %s (UTC)：' % (k + 1, ts[:16].replace('T', ' ')), '']
            L += [demote(clean(tx, sc)).rstrip(), '']
    text = '\n'.join(L).rstrip('\n') + '\n'
    text = '\n'.join(ln.rstrip() for ln in text.split('\n'))
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, 'w', encoding='utf-8') as fh:
        fh.write(text)
    left = [m for m in re.findall(r'/(?:Users|private|home)/[^\s`"\')]*', text)]
    print('%s: %d 字符; 简报 %d; 回报 %s; 残留本机路径 %d' % (
        os.path.relpath(a.out, ROOT), len(text), len(r['brief']),
        [len(h[1]) for h in r['handbacks']] if not a.pending else '在跑', len(left)))
    if left:
        print('  残留:', left[:5])
        sys.exit(1)


if __name__ == '__main__':
    main()
