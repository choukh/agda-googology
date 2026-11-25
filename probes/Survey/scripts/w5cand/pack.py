# -*- coding: utf-8 -*-
# 把候选折叠的一整条链从 <src> 改名抄到 <dst>: 依赖候选定义的模块换新名, 其余原名共享.
import io, os, re, sys
src, dst = sys.argv[1], sys.argv[2]
roots = sys.argv[3:]
DEFS = {'W4Path': 'W5Path', 'W4Loc': 'W5Loc', 'W4Fold': 'W5Fold', 'W4Val': 'W5Val', 'W4View': 'W5View',
        'WVOne': 'W5VOne', 'WVTwo': 'W5VTwo'}
imp = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)', re.M)
mods = {}
def load(m):
    if m in mods: return
    p = os.path.join(src, m + '.agda')
    if not os.path.exists(p): return
    s = io.open(p, encoding='utf-8').read()
    mods[m] = (s, [x for x in imp.findall(s) if '.' not in x])
    for x in mods[m][1]: load(x)
for r in roots: load(r)
# 哪些模块 (传递地) 依赖候选定义
dep = {}
def needs(m, seen=()):
    if m in dep: return dep[m]
    if m in DEFS: dep[m] = True; return True
    if m not in mods: dep[m] = False; return False
    dep[m] = any(needs(x) for x in mods[m][1])
    return dep[m]
for m in list(mods): needs(m)
ren = dict(DEFS)
for m in mods:
    if dep[m] and m not in ren:
        if m.startswith('K'): ren[m] = 'K5' + m[1:]
        else: ren[m] = 'W5' + m
ident = u"A-Za-z0-9_′⁼₀-₉'"
pat = re.compile(u'(?<![%s.])(%s)(?![%s])' % (ident, u'|'.join(sorted(map(re.escape, ren), key=len, reverse=True)), ident))
os.makedirs(dst, exist_ok=True)
out = []
for m, (s, _) in sorted(mods.items()):
    if dep[m]:
        s2 = pat.sub(lambda mo: ren[mo.group(1)], s)
        io.open(os.path.join(dst, ren[m] + '.agda'), 'w', encoding='utf-8').write(s2)
        out.append('%s -> %s' % (m, ren[m]))
    else:
        io.open(os.path.join(dst, m + '.agda'), 'w', encoding='utf-8').write(s)
        out.append('%s (shared)' % m)
print('\n'.join(out))
