# -*- coding: utf-8 -*-
# SumHt 的账, 口径同 probes/Survey/scripts/locslice_l12.py 与 sumone/locslice_sumone.py:
# 定义级切片, 计 agda 非空非注释行, 记号模块除外. 用法: python3 locslice_sumht.py <H>
import os,sys,io,collections
import os; here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
SH={'OCF.BTBO','OCF.Free.Level'}
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par,ex=False): return sum(lines(n) for n in par if n[0] not in NOT and (not ex or n[0] not in SH))
def bymod(ns,top=14):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
base=[(A+'CumReadCF','A'),(A+'CumReadCF','Lg')]
G=A+'SumHtGrow'
ROUTES={
 'SumOne (Ω+1)':([(A+'SumOneTree','D₊')]+base,[(A+'SumOneClosed','fgh'),(A+'SumOneClosed','ord')],[(A+'SumOneFold','Lg-T₁')],None),
 'SumHt (到 Ω², 一切 (p,a))':([(A+'SumHtTree','D₊')]+base,[(A+'SumHtClosed','fgh'),(A+'SumHtClosed','ord'),(A+'SumHtClosed','TΩ')],[(A+'SumHtClosed','Lg-T²'),(A+'SumHtClosed','Lg-T'),(A+'SumHtClosed','Lg-Tω'),(A+'SumHtClosed','Lg-TΩ')],
   [(G,'Ω+1<Ω+2'),(G,'Ω+2<Ω·2'),(G,'Ω·2<Ω·ω'),(G,'Ω·ω<Ω²'),(G,'lt-up'),(G,'lt-ω')]),
}
rows={}
for k,(l1,l2,l3,l4) in ROUTES.items():
    P1=C(l1); P2=C(l2)|P1; P3=C(l3)|P2
    out='%s | 层1 %d (去共用 %d) | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(k,T(P1),T(P1,True),T(P2),T(P2,True),T(P3),T(P3,True))
    if l4:
        P4=C(l4)|P3; out+=' | 加严格增长 %d (净增 %d)'%(T(P4),T(P4)-T(P3)); rows[k]=(P1,P2,P3,P4)
    else: rows[k]=(P1,P2,P3,P3)
    print(out)
k='SumHt (到 Ω², 一切 (p,a))'
P1,P2,P3,P4=rows[k]
print('层1 按模块:',bymod(P1)); print('层2 净增按模块:',bymod(P2-P1)); print('层3 净增按模块:',bymod(P3-P2)); print('严格增长净增按模块:',bymod(P4-P3))
leg=C([(A+'SumHtTree','Lg-sum')])
print('Lg-sum 切片 %d 行, 其中 SumHtTree 内 %d 行'%(T(leg),sum(lines(n) for n in leg if n[0]==A+'SumHtTree')))
for m in ('SumOneTree','SumHtTree'):
    P=C([(A+m,'D₊'),(A+m,'D'),(A+m,'D̂'),(A+m,'Dl')]+base)
    print('层1 (含层的类型 D, D̂, Dl)',m,T(P))
