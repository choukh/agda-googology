# -*- coding: utf-8 -*-
"""原事件回灌的成本校准；不是全种类候选或完整 View 的成本。

先成功生成 EvFoldClosed 的 Agda HTML，再运行本脚本 <HTML目录>。
复用仓库 locslice；对可达本地模块的全部模块别名补根到不动点。
不排除任何本地模块，标准库不计；报告仍是语法切片近似。
"""
from collections import Counter
from pathlib import Path
import sys

framework = Path(__file__).resolve().parents[1] / 'locslice.py'
if len(sys.argv) != 2:
    raise SystemExit('用法: locslice_eventreturn.py <成功编译的HTML目录>')
html = Path(sys.argv[1])
assert (html / 'OCF.Align.EvFoldClosed.html').is_file(), html
ns = {'__file__': str(framework), '__name__': 'eventreturn_cost'}
exec(compile(framework.read_text().split('\nB4=')[0], str(framework), 'exec'), ns)
find, closure, chunk, lines = (ns[n] for n in ('find', 'closure', 'chunk', 'lines'))


def measure(label, roots):
    for root in roots:
        assert find(*root), ('找不到根', root)
    reached = closure(roots)
    aliases = set()
    while True:
        extra = set()
        for mod in {m for m, _ in reached if m.startswith('OCF.')}:
            for c in chunk(mod).chunks:
                if c['name'].startswith('module ') and any(' = ' in s for s in c['text']):
                    extra.add((mod, c['name']))
        extra -= aliases
        if not extra:
            break
        aliases |= extra
        reached |= closure(sorted(extra))
    sizes = Counter()
    for node in reached:
        if node[0].startswith('OCF.'):
            assert (html / (node[0] + '.html')).is_file(), ('缺少依赖HTML', node[0])
            sizes[node[0]] += lines(node)
    print(label, '本地代码', sum(sizes.values()), '本地模块', len(sizes),
          '模块别名补根', len(aliases))
    print('  ', ', '.join('%s %d' % p for p in sizes.most_common()))
    print('  别名根:', ', '.join('%s:%s' % p for p in sorted(aliases)))


A = 'OCF.Align.'
measure('原两个读回、合法性与迁回', [(A + 'EvFoldRead', n) for n in
        ('rd₁', 'rd₂', 'Lg-rd₁', 'Lg-rd₂', 'drp₁', 'drp₂')])
measure('原双事件闭项和FGH；不含新增高层View',
        [(A + 'EvFoldClosed', 'fgh'), (A + 'EvFoldClosed', 'Lg-T-Ω₃²')])
