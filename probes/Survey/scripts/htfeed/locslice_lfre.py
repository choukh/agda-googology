# -*- coding: utf-8 -*-
# LFRe 的账, 口径同 htfeed/locslice_htfeed.py (复制自 httower/locslice_httower.py). 用法: python3 locslice_lfre.py <H>
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

Y=A+'LFReTy'; W=A+'LFReTower'; B=A+'LFReBr'; NG=A+'LFReNeg'
def rep(lbl,P,prev=None):
    if prev is None: print('%s %d (去共用 %d): %s'%(lbl,T(P),T(P,True),bymod(P)))
    else: print('%s %d (去共用 %d), 净增 %d: %s'%(lbl,T(P),T(P,True),T(P)-T(prev),bymod(P-prev)))
# 层 1: 层号与高度的定义 (块, SL, Ω̂, 塔, Λ, 不动点)
P1=C([(Y,'LH'),(Y,'Lv'),(Y,'SL'),(W,'Ω̂'),(W,'Λ'),(W,'fix'),(W,'Λn')])
rep('层1 定义',P1)
# 层 2: + 折叠, 闭项, FGH (经 toH 用 HtFeedClosed)
P2=C([(B,'ψ₀ᴸ'),(B,'ψ₀Ω₁'),(B,'fgh')])|P1
rep('层2 +折叠/闭项/FGH',P2,P1)
# 层 3: + 合法 (高度合法, 比较, 闭项合法)
P3=C([(W,'Lg-Λ'),(W,'Lg-Λn'),(W,'Lg-fix'),(W,'cmpL'),(B,'Lg-ψ₀ᴸ'),(B,'Lg-toH')])|P2
rep('层3 +合法',P3,P2)
# 层 3 去掉折叠: 只有高度这一层
Q=C([(W,'Lg-Λ'),(W,'Lg-Λn'),(W,'Lg-fix'),(W,'cmpL')])|P1
rep('高度层 定义+合法 (不含折叠)',Q,P1)
# 互通与链点
RR=C([(B,'Lg-ofH'),(B,'Lg-chainω'),(B,'Lg-chain₀'),(B,'fst-chain₀'),(Y,'E-rbl')])|P3
rep('+互通/链点/E-rbl',RR,P3)
Qn=C([(NG,n) for n in ['no-canon','Lg-dup','no-bare','no-retract-SL']])
print('否定 (独立切片) %d: %s'%(T(Qn),bymod(Qn)))
for n in ['no-canon','no-bare','no-retract-SL']:
    print('  %s %d'%(n,T(C([(NG,n)]))))
