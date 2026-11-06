# -*- coding: utf-8 -*-
# DiagK 的账, 口径同 htfeed/locslice_htfeed.py. 用法 (仓库根目录): python3 <本脚本> <H>
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
def bymod(ns,top=14):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
def row(name,l1,l2,l3):
    P1=C(l1);P2=C(l2)|P1;P3=C(l3)|P2
    print('%s | 层1 %d (去共用 %d) | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(name,T(P1),T(P1,True),T(P2),T(P2,True),T(P3),T(P3,True)))
    print('  层2 按模块:',bymod(P2)); print('  层3 按模块:',bymod(P3))
    return P3
D=A+'DiagKTop'; I=A+'DiagKInst'; Su=A+'DiagKSum'
P=row('条件候选 Top.Tᴰ (towerL′)',[(D,'Tower'),(D,'LevelFold'),(D,'towerL′')],[(D,'fgh'),(D,'towerL′')],[(D,'Lg-Tᴰ'),(D,'Lg-λh')])
P=row('实例 Tdg₂',[(Su,'Dg'),(A+'CumReadCF','Lg')],[(I,'fgh₂')],[(I,'Lg-Tdg₂')])
for m,n in [(Su,'Dg≈sup'),(Su,'glitch'),(A+'DiagKPos','off'),(A+'DiagKPos','rl-inj'),(A+'DiagKPos','bnd-up'),(A+'DiagKLev','updL′→wdec'),(D,'Lg-blind')]:
    Q=C([(m,n)]); print('独立切片 %s:%s %d: %s'%(m.replace(A,''),n,T(Q),bymod(Q)))
