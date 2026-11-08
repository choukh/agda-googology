# -*- coding: utf-8 -*-
"""真实树侧融合的成对依赖切片，非1513完整成品认证。

成功对 TreeEmitBuildAccept 生成全部高亮HTML后，运行本脚本 <HTML目录>。
旧侧取V、GV、force-HS、FGH及实际HB ω²；新侧取closed/legal/fgh。
记录字段与模块参数存在隐式依赖，补可达模块别名至不动点；结果仍为
语法近似。两侧均计本地依赖、均不计标准库，禁止当作新强度证据。
"""
import collections
import io
import os
import sys

base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'locslice.py')
source = io.open(base, encoding='utf-8').read().split('\nB4=')[0]
# 原切块器不识别opaque。两词长度均为6，保持HTML字符位置不变，
# 只对切块视图当作mutual，不修改源码或Agda语义。
source = source.replace("f.text=io.open(p,encoding='utf-8').read()",
    "f.text=re.sub(r'(?m)^([ \\t]*)opaque(?=[ \\t]*$)', r'\\1mutual', io.open(p,encoding='utf-8').read())")
__file__ = base
exec(source)

A = 'OCF.Align.'
common = [(A + 'LadderOrdPos', 'HB'), (A + 'LadderOrdCode', 'ω²ᶜ')]
old_roots = [(A + 'ValLabLadder', 'V'), (A + 'ValLabLadder', 'GV'),
             ('OCF.Free.Force', 'forceᴺ-HS'), ('OCF.Free.Level', 'FGH')] + common
new_roots = [(A + 'TreeEmitBuildClosed', x) for x in ['closed', 'closed-legal', 'fgh']]

def sliced(roots):
    for module, name in roots:
        if not find(module, name):
            raise SystemExit('MISSING ROOT: ' + module + ':' + name)
    result = closure(roots)
    supplemental = set()
    while True:
        found = set()
        for module in {m for m, _ in result}:
            for entry in chunk(module).chunks:
                if entry['name'].startswith('module ') and ' = ' in entry['text'][0]:
                    found.add((module, entry['name']))
        extra = found - supplemental
        if not extra:
            break
        supplemental |= extra
        result |= closure(sorted(extra))
    missing = sorted({m for m, _ in result if not os.path.isfile(os.path.join(H, m + '.html'))})
    if missing:
        raise SystemExit('MISSING HTML: ' + ', '.join(missing))
    return result, supplemental

old, old_aliases = sliced(old_roots)
new, new_aliases = sliced(new_roots)

def count(nodes):
    return sum(lines(node) for node in nodes)

for label, nodes, roots, aliases in [('OLD', old, old_roots, old_aliases),
                                   ('NEW', new, new_roots, new_aliases)]:
    print(label, 'ROOTS', roots)
    print(label, 'LINES', count(nodes), 'MODULES', len({m for m, _ in nodes}),
          'ALIASES', len(aliases))
    detail = collections.Counter()
    for node in nodes:
        detail[node[0]] += lines(node)
    print(label, 'DETAIL', sorted(detail.items()))
    for module, name in [('OCF.Free.Force', 'Goodᴺ'), (A + 'LadderOrdMain', 'GᴺTᵠ'),
                         (A + 'LadderOrdTree', 'ψ̄ᵠ'), (A + 'TreeEmitBuild', 'sound'),
                         ('OCF.Free.OrbitRewriteBuild', 'move')]:
        print(label, 'REACHES', module + ':' + name, bool(set(find(module, name)) & nodes))
print('DELTA', count(new) - count(old))
for label, nodes in [('REMOVED', old - new), ('ADDED', new - old)]:
    print(label, count(nodes))
    for module, index in sorted(nodes):
        print(' ', module, chunk(module).chunks[index]['name'], lines((module, index)))
