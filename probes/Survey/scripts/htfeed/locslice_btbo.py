import os,sys,io,collections
import os; here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def T(par): return sum(lines(n) for n in par if n[0] not in NOT)
def bymod(ns):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%kv for kv in c.most_common(8))
for nm,roots in [('BTBOᴵ 定义',[(A+'NoCumsum','BTBOᴵ')]),('BTBOᴵ 加证书',[(A+'NoCumsum','BTBOᴵ'),(A+'NoCumsum','BTBO-HS')]),('src BTBO',[('OCF.BTBO','BTBO')]),('src BTBO FGH',[('OCF.BTBO','FGH'),('OCF.BTBO','BTBO')])]:
    ok=all(find(m,n) for m,n in roots)
    P=closure(roots); print(nm, 'found' if ok else 'MISSING', T(P), '|', bymod(P))
