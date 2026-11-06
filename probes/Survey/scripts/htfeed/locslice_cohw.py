# -*- coding: utf-8 -*-
# CohW 的账, 口径同 htfeed/locslice_htfeed.py (复制自 htfeed/locslice_lfre.py). 用法: python3 locslice_cohw.py <H>
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
def rep(lbl,P,prev=None):
    if prev is None: print('%s %d (去共用 %d): %s'%(lbl,T(P),T(P,True),bymod(P)))
    else: print('%s %d (去共用 %d), 净增 %d: %s'%(lbl,T(P),T(P,True),T(P)-T(prev),bymod(P-prev)))
Y=A+'CohWTy'; L=A+'CohWL'; W=A+'CohWTower'; N=A+'CohWNeg'; G=A+'CohWGl'; U=A+'CohWUpd'
print('--- U⋆ 一路 ---')
P1=C([(L,'U⋆'),(W,'θ⋆'),(W,'Λ⋆')]); rep('层1 定义 (U⋆, 塔, 对角)',P1)
P3=C([(W,'Lg-Λ⋆')])|P1; rep('层3 +合法',P3,P1)
M=C([(L,n) for n in ['kmU','wmU','needU','wmatchU','tri','rcohL→','rcohL←','yes-wmatch','coh']]); rep('对应与相干 (独立切片)',M)
Ac=C([(W,'accΛ⋆')]); rep('层的良基 (独立切片)',Ac)
Ng=C([(N,n) for n in ['no-cross→','no-cross←','no-route','no-route←','no-crossA→','no-crossA←','Lg-κL-layer']]); rep('否定与 κL 层 (独立切片)',Ng)
print('--- SL⋆ 一路 ---')
Q1=C([(G,'SL⋆'),(G,'Λ'),(G,'Λn')]); rep('层1 定义 (块, GW, SL⋆, Ω̂, 塔, Λ)',Q1)
Q3=C([(G,'Lg-Λ'),(G,'Lg-Λn'),(G,'cmpL⋆')])|Q1; rep('层3 +合法',Q3,Q1)
QM=C([(G,n) for n in ['kmS','wmS','glob','globPr','cross','cross-ex']]); rep('对应与相干 (独立切片)',QM)
QU=C([(U,'upd→wdec')]); rep('upd→wdec (独立切片)',QU)
