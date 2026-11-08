# -*- coding: utf-8 -*-
"""输出驱动闭项的前三层切片；不把验收值证明当作成品根。

用成功编译 OutputDrivenGrid 所得的 --html-highlight=all HTML 作输入。
继承 third/locslice_third.py 对 CRw 仅使用 FGH 的处理；所有可达本地
模块的模块别名补根到不动点。原参数化折叠/路径的实际算法手工补根。
这是语法近似，未计尚未交付的内部 View，不是完整成品的预算认证。
"""
from collections import Counter
from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit('用法: locslice_outputdriven.py <成功编译的HTML目录>')
html = Path(sys.argv[1])
assert (html / 'OCF.Lean.OutputDrivenGrid.html').is_file(), html
framework = Path(__file__).resolve().parents[1] / 'locslice.py'
ns = {'__file__': str(framework), '__name__': 'outputdriven_cost'}
exec(compile(framework.read_text().split('\nB4=')[0], str(framework), 'exec'), ns)
original_succ = ns['succ']


def successors(node):
    result = original_succ(node)
    if node[0] != 'OCF.Lean.CRw':
        return result
    c = ns['chunk'](node[0])
    opened = set(c.chunks[c.rootc].get('opens', []))
    return [x for x in result if not (x[0] == node[0] and x[1] in opened)]


ns['succ'] = successors
find, closure, chunk, lines = (ns[n] for n in ('find', 'closure', 'chunk', 'lines'))


def roots(module, names):
    return [('OCF.Lean.' + module, name) for name in names.split()]


manual = (roots('ThirdFold', 'Φ Sh-Φ') + roots('ThirdSan', 'Er ph-san ph-tp') +
          roots('ThirdPath', 'PH-Φ') + roots('ThirdX', 'ΦX Sh-ΦX PH-ΦX↓'))


def measure(label, initial):
    initial = initial + manual
    for root in initial:
        assert find(*root), ('找不到根', root)
    reached = closure(initial)
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
            assert (html / (node[0] + '.html')).is_file(), ('缺依赖HTML', node[0])
            sizes[node[0]] += lines(node)
    print(label, '本地代码', sum(sizes.values()), '本地模块', len(sizes),
          '别名补根', len(aliases))
    print('  ', ', '.join('%s %d' % item for item in sizes.most_common()))
    print('  手工参数根:', ', '.join('%s:%s' % x for x in manual))
    print('  别名根:', ', '.join('%s:%s' % x for x in sorted(aliases)))
    return reached


diagonal = measure('同步对角闭项及合法FGH；未含新增内部View',
        roots('OutputDrivenClosed', 'closed legal-closed fgh'))
grid = measure('全方格闭项及合法FGH；未含新增内部View',
        roots('OutputDrivenGrid', 'closedGrid legal-closedGrid fghGrid'))
