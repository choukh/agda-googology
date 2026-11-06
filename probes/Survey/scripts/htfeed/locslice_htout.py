# -*- coding: utf-8 -*-
# HtOut 的账, 口径同 sumht/locslice_climb.py, htfeed/locslice_htfeed.py. 用法: python3 locslice_htout.py <H>
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
# HtFeed 原来的层 (对照)
f2=[(A+'HtFeedClosed','fgh'),(A+'HtFeedClosed','TΛ'),(A+'HtFeedClosed','T-Ω'),(A+'HtFeedClosed','T-Ωk'),(A+'HtFeedClosed','T-ΩΩk')]
f3=[(A+'HtFeedClosed','Lg-TΛ')]
F1=C(l1);F2=C(f2)|F1;F3=C(f3)|F2
print('HtFeed | 层1 %d | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(T(F1),T(F2),T(F2,True),T(F3),T(F3,True)))
# HtOut: 闭项的高度只由回灌生成
o2=[(A+'HtOutFeed','fgh'),(A+'HtOutFeed','T-fbω'),(A+'HtOutFeed','T-fb')]
o3=[(A+'HtOutFeed','Lg-T-fbω')]
P1=C(l1);P2=C(o2)|P1;P3=C(o3)|P2
print('HtOut | 层1 %d | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(T(P1),T(P2),T(P2,True),T(P3),T(P3,True)))
print('HtOut 层2 按模块:',bymod(P2))
print('HtOut 层2 不在 HtFeed 层2 的:',T(P2-F2),bymod(P2-F2))
print('HtFeed 层2 不在 HtOut 层2 的:',T(F2-P2),bymod(F2-P2))
G=A+'HtOutGrow'
for nm in ['Λ-st','Λ-Ω','Sup-fb','Sup-ω']:
    Q=C([(G,nm)])|P3
    print('增长 %s: 加 %d 行'%(nm,T(Q)-T(P3)))
Q=C([(G,n) for n in ['Λ-st','Λ-Ω','Sup-fb','Sup-ω']])|P3
print('全部增长 净增 %d: %s'%(T(Q)-T(P3),bymod(Q-P3)))
N=A+'HtOutNeg'
Q=C([(N,n) for n in ['drop-lim','drop-suc','no-total']])
print('否定 (独立切片) %d: %s'%(T(Q),bymod(Q)))
R=A+'HtOutRead'
Q=C([(R,'rd'),(R,'Lg-rd')])
print('读法+合法 (独立切片) %d: %s'%(T(Q),bymod(Q)))
Q=C([(R,'cont→LgH')])
print('cont→LgH (独立切片) %d: %s'%(T(Q),bymod(Q)))
print('层2 里 HtFeedHt 的块:',[ (chunk(n[0]).chunks[n[1]]['name'],lines(n)) for n in P2 if n[0]==A+'HtFeedHt'])
par=bfs(find(A+'HtOutFeed','T-fbω'))
for n in par:
    if n[0]==A+'HtFeedHt': print('  路径:',path(par,n))
