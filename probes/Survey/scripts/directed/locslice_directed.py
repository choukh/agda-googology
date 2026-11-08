# -*- coding: utf-8 -*-
"""定向简化的同口径执行切片；不把值比较证明计入运行根。

先成功运行 agda --html --html-highlight=all --html-dir=<H> ...
    probes/Survey/EBOEndgame.lagda.md +RTS -M6G -RTS
再运行 python3 probes/Survey/scripts/directed/locslice_directed.py <H>。
两侧都只取 E.Ord 闭项及其 E.FGH，标准库同既有脚本不计。
这不是 1513 标杆的四层全根重算，也不是无记号审计。
"""
import collections
import io
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
base = os.path.join(here, '..', 'locslice.py')
source = io.open(base, encoding='utf-8').read().split('\nB4=')[0]
__file__ = base
exec(source)

A = 'OCF.Align.'
tree = A + 'EboLean3Tree'
new = A + 'DirectedViewBuildClosed'
direct = A + 'DirectedViewDirectClosed'
aliases = []
for module in [A + 'EboLean3' + suffix for suffix in ['Base', 'Close', 'Dist', 'Omega']]:
    for entry in chunk(module).chunks:
        if entry['name'].startswith('module ') and ' = ' in entry['text'][0]:
            aliases.append((module, entry['name']))
            print('ALIAS-ROOT', module, entry['name'])

def slice_for(roots):
    for module, name in roots + aliases:
        if not find(module, name):
            raise SystemExit('MISSING ROOT: ' + module + ':' + name)
    reached = closure(roots + aliases)
    missing = sorted({module for module, _ in reached
                      if not os.path.isfile(os.path.join(H, module + '.html'))})
    if missing:
        raise SystemExit('MISSING HTML: ' + ', '.join(missing))
    return reached

old_roots = [(tree, 'EBO-tree″'), (tree, 'FGH')]
new_roots = [(new, 'program'), (tree, 'FGH')]
old = slice_for(old_roots)
changed = slice_for(new_roots)
direct_roots = [(direct, 'program'), (tree, 'FGH')]
final = slice_for(direct_roots)

def count(nodes):
    return sum(lines(node) for node in nodes)

bridges = [(A + 'EboLeanDef', 'HC'), (A + 'EboLeanDef', 'fsn'),
           (A + 'EBO', 'fsT'), (A + 'EBO', 'γT'),
           (A + 'EboLeanView', 'fω-eq'), (A + 'EboLeanView', 'fΩ-eq'),
           (A + 'EboLeanView', 'γ-eq')]
for label, nodes, roots in [('OLD', old, old_roots), ('CACHED', changed, new_roots),
                            ('DIRECT', final, direct_roots)]:
    print(label, 'ROOTS', roots)
    print(label, 'LINES', count(nodes), 'MODULES', len({m for m, _ in nodes}))
    print(label, 'HC REACHED', bool(find(A + 'EboLeanDef', 'HC') and
                                   set(find(A + 'EboLeanDef', 'HC')) & nodes))
    print(label, 'BRIDGES', {module + ':' + name: bool(set(find(module, name)) & nodes)
                             for module, name in bridges})
    print(label, 'DETAIL', sorted(collections.Counter(
        {module: sum(lines(n) for n in nodes if n[0] == module)
         for module in {m for m, _ in nodes}}).items()))
print('CACHED DELTA', count(changed) - count(old))
print('DIRECT DELTA', count(final) - count(old))
for label, nodes in [('DIRECT REMOVED', old - final), ('DIRECT ADDED', final - old)]:
    print(label, count(nodes))
    for module, index in sorted(nodes):
        print(' ', module, chunk(module).chunks[index]['name'], lines((module, index)))
