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

# HtTotal: 回灌的 Ω-迭代
t2=[(A+'HtTotalIter','fgh'),(A+'HtTotalIter','T-T'),(A+'HtTotalIter','T-Ω'),(A+'HtTotalIter','T-Ω₀'),(A+'HtTotalIter','T-Λ²ω')]
t3=[(A+'HtTotalIter','Lg-T-T')]
Q1=C(l1);Q2=C(t2)|Q1;Q3=C(t3)|Q2
print('HtTotal | 层1 %d | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(T(Q1),T(Q2),T(Q2,True),T(Q3),T(Q3,True)))
print('HtTotal 层2 按模块:',bymod(Q2))
print('HtTotal 层2 不在 HtOut 层2 的:',T(Q2-P2),bymod(Q2-P2))
print('HtOut 层2 不在 HtTotal 层2 的:',T(P2-Q2),bymod(P2-Q2))
print('HtTotal 层3 - 层2:',T(Q3)-T(Q2),bymod(Q3-Q2))
I=A+'HtTotalIter'
for nm in ['Sup-Ω₀','Sup-Ω','Sup-Tk']:
    Q=C([(I,nm)])|Q3
    print('增长 %s: 加 %d 行'%(nm,T(Q)-T(Q3)))
Q=C([(I,n) for n in ['Sup-Ω₀','Sup-Ω','Sup-Tk']])|Q3
print('全部增长 净增 %d: %s'%(T(Q)-T(Q3),bymod(Q-Q3)))
N=A+'HtTotalNeg'
Q=C([(N,n) for n in ['no-clamp','no-valid','no-agree']])
print('否定 (独立切片) %d: %s'%(T(Q),bymod(Q)))
Q=C([(N,n) for n in ['no-clamp','no-valid']])
print('否定 no-clamp+no-valid (独立) %d: %s'%(T(Q),bymod(Q)))
K=A+'HtTotalClamp'
Q=C([(K,'cl'),(K,'Lg-cl')])
print('夹法+合法 (独立切片) %d: %s'%(T(Q),bymod(Q)))
Q=C([(K,'Fbᶜ'),(K,'Good-Fbᶜ')])
print('Fbᶜ+Good (独立切片) %d: %s'%(T(Q),bymod(Q)))
Q=C([(K,'agree-fin'),(K,'TΛᶜ-fin')])
print('一致 (独立切片) %d: %s'%(T(Q),bymod(Q)))
