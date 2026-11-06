# -*- coding: utf-8 -*-
# CohW2 的账, 口径同 htfeed/locslice_htfeed.py (复制自 htfeed/locslice_lfre.py). 用法: python3 locslice_cohw.py <H>
import os,sys,io,collections
here=os.path.join(os.getcwd(),'probes','Survey','scripts')  # 从仓库根目录运行
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
N=A+'CohW2Need'; M=A+'CohW2Lim'; G=A+'CohW2Grow'
for lbl,ms in [('raise-Lc→WLPO',[(N,'raise-Lc→WLPO')]),('raise-Lc→wdec',[(N,'raise-Lc→wdec')]),('raiseFin+raise-nat',[(N,'raiseFin'),(N,'raise-nat')]),
               ('lim-layer+Lg-lim-layer+Lg-hα',[(M,'lim-layer'),(M,'Lg-lim-layer'),(M,'Lg-hα')]),('growA+⊞⁰-fst',[(G,'growA'),(G,'⊞⁰-fst')]),
               ('全部',[(N,'raise-Lc→WLPO'),(N,'raiseFin'),(N,'raise-nat'),(M,'Lg-lim-layer'),(M,'Lg-hα'),(G,'growA'),(G,'⊞⁰-fst')])]:
    rep(lbl,C(ms))
