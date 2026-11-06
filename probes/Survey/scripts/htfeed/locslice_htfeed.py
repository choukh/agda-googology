# -*- coding: utf-8 -*-
# HtFeed 的账, 口径同 locslice_l12.py / sumht/locslice_climb.py. 用法: python3 locslice_htfeed.py <H>
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
l1=[(A+'HtFeedTree','D₊'),(A+'HtFeedTree','D'),(A+'HtFeedTree','H')]+base
l2=[(A+'HtFeedClosed','fgh'),(A+'HtFeedClosed','TΛ'),(A+'HtFeedClosed','T-Ω'),(A+'HtFeedClosed','T-Ωk'),(A+'HtFeedClosed','T-ΩΩk')]
l3=[(A+'HtFeedClosed','Lg-TΛ')]
P1=C(l1);P2=C(l2)|P1;P3=C(l3)|P2
print('HtFeed | 层1 %d | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(T(P1),T(P2),T(P2,True),T(P3),T(P3,True)))
print('层2 按模块:',bymod(P2))
G=A+'HtFeedGrow'
for nm in ['Sup','SupStmt','Sup-Ω','Sup-Ω·2','Sup-ΩΩk','feed']:
    Q=C([(G,nm)])|P3
    print('增长 %s: 加 %d 行'%(nm,T(Q)-T(P3)))
Q=C([(G,n) for n in ['Sup-Ω','Sup-Ω·2','Sup-ΩΩk','feed']])|P3
print('全部增长 净增 %d: %s'%(T(Q)-T(P3),bymod(Q-P3)))
N=A+'HtFeedNeg'
Q=C([(N,n) for n in ['no-weak','no-glob','no-world-top']])
print('否定 (独立切片) %d: %s'%(T(Q),bymod(Q)))
