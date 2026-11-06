# -*- coding: utf-8 -*-
# HtTowerF 的账, 口径同 htfeed/locslice_htfeed.py. 用法: python3 locslice_httowerf.py <H>
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
Tr=A+'HtTowerFTree'; Cl=A+'HtTowerFClosed'
l1=[(Tr,'D₊'),(Tr,'D'),(Tr,'Ht'),(Tr,'Wd₂'),(Tr,'StH'),(A+'CumReadCF','A'),(A+'CumReadCF','Lg')]
l2=[(Cl,'fgh'),(Cl,'TΛ'),(Cl,'T⁺'),(Cl,'T-Ω₂')]
l3=[(Cl,'Lg-TΛ'),(Cl,'Lg-T⁺'),(Cl,'Lg-T-Ω₂²')]
P1=C(l1);P2=C(l2)|P1;P3=C(l3)|P2
print('HtTowerF | 层1 %d (去共用 %d) | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(T(P1),T(P1,True),T(P2),T(P2,True),T(P3),T(P3,True)))
print('层1 按模块:',bymod(P1))
print('层2 按模块:',bymod(P2))
print('层3 净增:',bymod(P3-P2))
G=A+'HtTowerFGrow'
Q=C([(G,n) for n in ['Supμ-Ω₂','Sup-Ω₂','Sup-Ω₂+Ω']])|P3
print('增长 净增 %d: %s'%(T(Q)-T(P3),bymod(Q-P3)))
Q2=C([(A+'HtTowerFNeed','need-1')])
print('Need (独立) %d: %s'%(T(Q2),bymod(Q2)))
# 新种类专用的部分: Cut₁, IW₁, Walk₁, RunM 一族, rd/drp₁
F=A+'HtTowerFFold'
for nm in [(Tr,'Cut₁'),(Tr,'IW₁'),(F,'Walk₁'),(F,'RunM'),(A+'HtTowerFRead','rd'),(A+'HtTowerFRead','drp₁')]:
    print('  %s:%s 独立 %d'%(nm[0].replace(A,''),nm[1],T(C([nm]))))
