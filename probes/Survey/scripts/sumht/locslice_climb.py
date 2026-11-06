# -*- coding: utf-8 -*-
# SumClimb 的账, 口径同 locslice_l12.py. 用法: python3 locslice_climb.py <H>
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
def lay1(m): return [(A+m,'D₊'),(A+m,'D'),(A+m,'D̂'),(A+m,'Dl')]+base
rows=[
 ('SumHt',lay1('SumHtTree'),[(A+'SumHtClosed','fgh'),(A+'SumHtClosed','TΩ')],[(A+'SumHtClosed','Lg-T²'),(A+'SumHtClosed','Lg-T'),(A+'SumHtClosed','Lg-Tω'),(A+'SumHtClosed','Lg-TΩ')]),
 ('SumClimb',lay1('SumClimbTree'),[(A+'SumClimbClosed','fgh'),(A+'SumClimbClosed','TΩ')],[(A+'SumClimbClosed','Lg-T³'),(A+'SumClimbClosed','Lg-T'),(A+'SumClimbClosed','Lg-Tω'),(A+'SumClimbClosed','Lg-TΩ')]),
]
RR={}
for k,l1,l2,l3 in rows:
    P1=C(l1);P2=C(l2)|P1;P3=C(l3)|P2;RR[k]=(P1,P2,P3)
    print('%s | 层1 %d | 层2 %d (去共用 %d) | 层3 %d (去共用 %d)'%(k,T(P1),T(P2),T(P2,True),T(P3),T(P3,True)))
P1,P2,P3=RR["SumClimb"]
print('SumClimb 层2 按模块:',bymod(P2))
print('SumClimb 与 SumHt 不共用的层 3 行:',T(P3-RR["SumHt"][2]),bymod(P3-RR["SumHt"][2]))
G=A+'SumClimbGrow'
for nm in ['Ω²<Ω²+1','Ω²+1<Ω²·2','Ω²·2<Ω²·ω','Ω²·ω<Ω³','SupN','SupR','Sup3']:
    Q=C([(G,nm)])|P3
    print('严格增长 %s: 加 %d 行'%(nm,T(Q)-T(P3)))
Q=C([(G,n) for n in ['Ω²<Ω²+1','Ω²+1<Ω²·2','Ω²·2<Ω²·ω','Ω²·ω<Ω³','SupN','SupR','Sup3']])|P3
print('全部增长 净增 %d: %s'%(T(Q)-T(P3),bymod(Q-P3)))
# 每站闭项的行数 (站本身的定义块)
for nm in ['TΩ²+1','TΩ²·2','TΩ²·ω','TΩ³','X','XRω','Xω','X³','BR','B','κR','κ3','κB','κN']:
    Q=C([(A+'SumClimbClosed',nm)])
    print('站 %s 切片 %d, 其中 SumClimbClosed 内 %d'%(nm,T(Q),sum(lines(n) for n in Q if n[0]==A+'SumClimbClosed')))
