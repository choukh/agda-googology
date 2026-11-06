# -*- coding: utf-8 -*-
# 把 extract.py 的摘录渲染成几份便于阅读的 markdown 摘要 (写进 --out 目录, 不进仓库).
#
# 用法:
#   python3 probes/Survey/scripts/handbook/digest.py --ex <摘录目录> --out <摘要目录> [--since 2026-11-05] [--tz 8]
#
# --since 只看这一天 (本地时间) 之后的条目, 用于增量蒸馏: 上次蒸馏之后新来的子智能体报告, 作者消息, 报错.
# --tz 本地时区相对 UTC 的小时数 (记录里是 UTC; LOG.md 与地图用本地日期), 默认 8.
#
# 生成:
#   human.md        作者消息, 按时间
#   ask.md          选项工具的问答; 末尾统计 "作者选了推荐项" 的比例
#   dispatch.md     派发与续派, 按时间; 模型分布
#   reports.md      子智能体报告 (每路最后一份 handback, 没有就用最后一条正文), 只取开头
#   errors.md       报错分类计数, 堆耗尽清单, 每类前几条样例
#   agda.md         按模块族汇总: 运行次数, 用过的堆上限, 成功时的最大堆, 堆耗尽次数, 读到的用时
#   corrections.md  更正类语句
#   estimates.md    "估计 N 到 M 行" / "约 N 行" 一类的行数估计及上下文 (供和实际行数配对)
import argparse, collections, datetime, io, json, os, re

def load(ex, name):
    p = os.path.join(ex, name + '.jsonl')
    if not os.path.exists(p):
        return []
    out = []
    with io.open(p, encoding='utf-8') as f:
        for l in f:
            try:
                out.append(json.loads(l))
            except ValueError:
                pass
    return out

def loc(ts, tz):
    if isinstance(ts, (int, float)):
        d = datetime.datetime.utcfromtimestamp(ts)
    else:
        try:
            d = datetime.datetime.strptime(ts[:19], '%Y-%m-%dT%H:%M:%S')
        except (ValueError, TypeError):
            return '?'
    return (d + datetime.timedelta(hours=tz)).strftime('%Y-%m-%d %H:%M')

def one(s, n):
    s = (s or '').replace('\r', '').replace('\n', ' ⏎ ')
    return s if len(s) <= n else s[:n] + '…'

FAM = re.compile(r'^([A-Z][a-z0-9]+(?:[A-Z][a-z0-9]+)?)')

def family(fname):
    b = fname.replace('.lagda.md', '').replace('.agda', '')
    m = FAM.match(b)
    return m.group(1) if m else b

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ex', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--since', default='')
    ap.add_argument('--tz', type=int, default=8)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    tz = a.tz
    keep = lambda r: loc(r.get('ts'), tz) >= a.since

    def write(name, lines):
        with io.open(os.path.join(a.out, name), 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines) + '\n')

    # 作者消息
    H = [r for r in load(a.ex, 'human') if keep(r)]
    write('human.md', ['# 作者消息 (%d 条)' % len(H), ''] +
          ['- %s [%s] %s' % (loc(r['ts'], tz), r.get('source') or '', one(r['text'], 900)) for r in H])

    # 选项
    A = [r for r in load(a.ex, 'ask') if keep(r)]
    lines, rec, tot = ['# 选项工具 (%d 次)' % len(A), ''], 0, 0
    for r in A:
        try:
            q = json.loads(r['question'])
            qs = q.get('questions', [])
        except (ValueError, TypeError):
            qs = []
        ans = r.get('answer', '')
        picks = re.findall(r'"=\s*"(.*?)"(?:[,.]|$)', ans)
        notes = re.findall(r'user notes: (.*?)(?: You can|$)', ans)
        lines.append('## %s' % loc(r['ts'], tz))
        for x in qs:
            opts = [o.get('label', '') for o in x.get('options', [])]
            lines.append('- 问: %s' % one(x.get('question', ''), 400))
            lines.append('  - 选项: %s' % ' / '.join(opts))
        if 'rejected' in ans:
            lines.append('- 答: (作者拒绝作答, 要先澄清)')
        else:
            lines.append('- 答: %s' % ' | '.join(picks))
            for p in picks:
                tot += 1
                rec += ('(Recommended)' in p)
        if notes:
            lines.append('- 作者附言: %s' % one(' '.join(notes), 600))
        lines.append('')
    lines.append('统计: 已回答的子问题 %d 个, 其中所选含推荐项 %d 个 (多选时按整串计).' % (tot, rec))
    write('ask.md', lines)

    # 派发
    D = [r for r in load(a.ex, 'dispatch') if keep(r)]
    models = collections.Counter(r.get('model') for r in D if r.get('tool') == 'Agent')
    lines = ['# 派发 (%d 次 Agent, %d 次 SendMessage)' % (
        sum(1 for r in D if r.get('tool') == 'Agent'), sum(1 for r in D if r.get('tool') == 'SendMessage')),
        '', '模型: %s' % dict(models), '']
    for r in D:
        if r.get('tool') == 'Agent':
            lines.append('- %s **%s** model=%s bg=%s: %s' % (loc(r['ts'], tz), r.get('description'), r.get('model'),
                                                           r.get('background'), one(r.get('prompt'), 300)))
        elif r.get('tool') == 'SendMessage':
            lines.append('- %s → %s: %s' % (loc(r['ts'], tz), r.get('to'), one(r.get('message'), 300)))
    write('dispatch.md', lines)

    # 报告
    R = [r for r in load(a.ex, 'sub_report') if keep(r)]
    B = {r.get('agent'): r for r in load(a.ex, 'sub_brief')}
    last = collections.OrderedDict()
    for r in R:
        ag = r.get('agent')
        if r.get('kind2') == 'handback' or ag not in last or last[ag].get('kind2') != 'handback':
            last[ag] = r
    lines = ['# 子智能体报告 (%d 路)' % len(last), '']
    for ag, r in sorted(last.items(), key=lambda kv: kv[1].get('ts') or ''):
        meta = (B.get(ag) or {}).get('meta') or r.get('meta') or {}
        nhb = sum(1 for x in R if x.get('agent') == ag and x.get('kind2') == 'handback')
        lines.append('## %s %s (%s, model=%s, handback %d 次)' % (loc(r['ts'], tz), meta.get('description', ''),
                                                                ag, meta.get('model'), nhb))
        lines.append(one(r.get('text'), 1800))
        lines.append('')
    write('reports.md', lines)

    # 报错
    E = [r for r in load(a.ex, 'errors') if keep(r)]
    tags = collections.Counter(t for r in E for t in r.get('tags', []))
    bykind = collections.Counter((r.get('kind'), t) for r in E for t in r.get('tags', []))
    lines = ['# 报错 (%d 条)' % len(E), '', '分类: %s' % dict(tags.most_common()), '',
             '按来源: %s' % dict(bykind.most_common()), '']
    for t, _ in tags.most_common():
        lines.append('## %s' % t)
        for r in [x for x in E if t in x.get('tags', [])][:12]:
            lines.append('- %s %s `%s` :: %s' % (loc(r['ts'], tz), r.get('agent') or r.get('kind'),
                                               one(r.get('cmd'), 200), one(r.get('snippet'), 400)))
        lines.append('')
    write('errors.md', lines)

    # agda
    G = [r for r in load(a.ex, 'agda_runs') if keep(r)]
    fam = collections.defaultdict(lambda: dict(n=0, heaps=collections.Counter(), ok=[], exh=0, exh_heaps=[], durs=[]))
    def gb(h):
        if not h:
            return None
        v = float(h[:-1])
        return v / 1024 if h.endswith('M') else v
    for r in G:
        fs = r.get('files') or ['?']
        ex = r.get('exits') or []
        ok = bool(ex) and ex[-1] == '0'
        for fn in fs:
            if fn.startswith('<') or fn in ('?',):
                continue
            f = fam[family(fn)]
            f['n'] += 1
            f['heaps'][r.get('heap')] += 1
            if ok and gb(r.get('heap')):
                f['ok'].append(gb(r.get('heap')))
            if r.get('heap_exhausted') or (ex and ex[-1] == '251'):
                f['exh'] += 1
                f['exh_heaps'].append(r.get('heap'))
            f['durs'] += r.get('dur') or []
    lines = ['# agda 运行, 按模块族 (%d 次)' % len(G), '',
             '| 族 | 次数 | 用过的 -M | 成功时最大 -M (G) | 堆耗尽/251 次数 (当时的 -M) | 读到的用时 (末几个) |', '|---|---|---|---|---|---|']
    for k, f in sorted(fam.items(), key=lambda kv: -kv[1]['n']):
        lines.append('| %s | %d | %s | %s | %d %s | %s |' % (
            k, f['n'], ', '.join('%s×%d' % (h, c) for h, c in f['heaps'].most_common(4)),
            ('%.0f' % max(f['ok'])) if f['ok'] else '', f['exh'],
            ('(' + ', '.join(str(x) for x in f['exh_heaps'][:5]) + ')') if f['exh'] else '',
            ', '.join(f['durs'][-3:])))
    write('agda.md', lines)

    # 更正
    C = [r for r in load(a.ex, 'corrections') if keep(r)]
    lines = ['# 更正类语句 (%d 条)' % len(C), '']
    for r in C:
        lines.append('- %s %s %s: %s' % (loc(r['ts'], tz), r.get('who'), r.get('agent') or '', one(r.get('text'), 500)))
    write('corrections.md', lines)

    # 估计
    EST = re.compile(r'(?:估计|预计|约|大约|估)[^。\n]{0,30}?(\d[\d,]*)\s*(?:到|至|-|~|–)?\s*(\d[\d,]*)?\s*行')
    lines = ['# 行数估计 (供与实际配对)', '']
    for name in ('coord_text', 'sub_report'):
        for r in load(a.ex, name):
            if not keep(r):
                continue
            t = r.get('text') or ''
            for m in EST.finditer(t):
                s = max(0, m.start() - 120)
                lines.append('- %s %s %s: %s' % (loc(r['ts'], tz), name, r.get('agent') or '', one(t[s:m.end() + 60], 300)))
    write('estimates.md', lines)
    print('写出摘要到', a.out)

if __name__ == '__main__':
    main()
