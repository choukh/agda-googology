# -*- coding: utf-8 -*-
# ChainZ 的账, 口径同 diagk3/locslice_diagk3.py. 用法 (仓库根目录): python3 <本脚本> <H>
import os,sys,io,collections
here=os.path.join('probes','Survey','scripts')
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
def bymod(ns,top=16):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
def row(name,l1,l2,l3):
    P1=C(l1);P2=C(l2)|P1;P3=C(l3)|P2
    print('%s | 层1 %d (去共用 %d) | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(name,T(P1),T(P1,True),T(P2),T(P2,True),T(P3),T(P3,True)))
    print('  层3 按模块:',bymod(P3))
    return P3
Z=A+'ChainZClosed'; N=A+'ChainZNeg'; S=A+'ChainZStall'
L1=[(A+'HtTowerFTree','D₊'),(A+'HtTowerFTree','D'),(A+'HtTowerTy','HB'),(A+'CumReadCF','A'),(A+'CumReadCF','Lg')]
row('Zs-Ω₂² (种子取输出)',L1,[(Z,'fgh'),(Z,'Zs-Ω₂²')],[(Z,'Lg-Zs-Ω₂²')])
row('对照 HtTowerFClosed T-Ω₂²',L1,[(A+'HtTowerFClosed','fgh'),(A+'HtTowerFClosed','T-Ω₂²')],[(A+'HtTowerFClosed','Lg-T-Ω₂²')])
for m,n in [(N,'no-chain'),(N,'dich'),(N,'no-world'),(S,'stall')]:
    Q=C([(m,n)]); print('独立切片 %s:%s %d: %s'%(m.replace(A,''),n,T(Q),bymod(Q)))
