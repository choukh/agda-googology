# -*- coding: utf-8 -*-
# HtTower 的账, 口径同 htfeed/locslice_htfeed.py. 用法: python3 locslice_httower.py <H>
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
Ty=A+'HtTowerTy'; U=A+'HtTowerU'
# 类型层: 种类结构与高度 (step, sup, Lev), 不含合法
l1=[(Ty,'KS'),(Ty,'HB'),(Ty,'step'),(Ty,'sup'),(Ty,'Lev')]
P1=C(l1)
# 塔 (定义): L, U, θ, Λᵁ
l2=[(U,'Λᵁ')]
P2=C(l2)|P1
# + 合法
l3=[(U,'Lg-Λᵁ'),(A+'HtTowerTy','cmpB')]
P3=C(l3)|P2
print('类型层 %d (去共用 %d): %s'%(T(P1),T(P1,True),bymod(P1)))
print('+塔 %d (去共用 %d): %s'%(T(P2),T(P2,True),bymod(P2)))
print('+合法与比较 %d (去共用 %d): %s'%(T(P3),T(P3,True),bymod(P3)))
Q=C([(A+'HtTowerCont','cont→Lg'),(A+'HtTowerCont','Lg-Ωtop')])|P3
print('+连续 净增 %d: %s'%(T(Q)-T(P3),bymod(Q-P3)))
Q2=C([(A+'HtTowerStrat','θ-indep')])|Q
print('+分层 净增 %d: %s'%(T(Q2)-T(Q),bymod(Q2-Q)))
Q3=C([(A+'HtTowerU','Lg-old')])|Q2
print('+旧高度嵌入 净增 %d: %s'%(T(Q3)-T(Q2),bymod(Q3-Q2)))
N=A+'HtTowerNeg'
Qn=C([(N,n) for n in ['no-retract','drop-Ω','naive-illegal','no-joinᴮ','no-joinA']])
print('否定 (独立切片) %d: %s'%(T(Qn),bymod(Qn)))
for n in ['no-retract','drop-Ω','naive-illegal','no-joinᴮ','no-joinA']:
    print('  %s %d'%(n,T(C([(N,n)]))))
# 对照: HtFeed 的层 1
l1f=[(A+'HtFeedTree','H'),(A+'HtFeedTree','LgH'),(A+'HtFeedTree','cmpH')]
print('对照 HtFeedTree 的 H+LgH+cmpH %d'%T(C(l1f)))
