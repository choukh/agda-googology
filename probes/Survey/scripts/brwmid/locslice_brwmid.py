# -*- coding: utf-8 -*-
# BrwMid 与 SumOne 的定义和合法性行数. 口径同 ../locslice_tlrule.py.
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 BrwMidFold, BrwMidZero, SumOneClosed, 再 python3 locslice_brwmid.py <H>.
import os,sys,io,collections
here=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par): return sum(lines(n) for n in par if n[0] not in NOT)
def bymod(ns,top=10):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
for name,roots in [('BrwMid T₀,T₁ 定义',[(A+'BrwMidFold','T₀')]),('BrwMid Lg-T₁',[(A+'BrwMidFold','Lg-T₁')]),
                   ('SumOne T₀,T₁ 定义',[(A+'SumOneFold','T₀'),(A+'SumOneClosed','ω⋅')]),('SumOne Lg-T₁',[(A+'SumOneFold','Lg-T₁')])]:
    X=C(roots); print(name,T(X),':',bymod(X))
leg=C([(A+'BrwMidZero','Lg-⊞'),(A+'BrwMidZero','⊞-fst')])
print('BrwMid 合法性 (⊞-fst, Lg-⊞) 切片',T(leg),':',bymod(leg))
leg2=C([(A+'SumOneTree','Lg-sum')])
print('SumOne 合法性 (Lg-sum) 切片',T(leg2),':',bymod(leg2))
d=C([(A+'BrwMidZero','dif')]); print('BrwMid dif (读回输入) 切片',T(d))
