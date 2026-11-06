# -*- coding: utf-8 -*-
# Fold1 一路的分层行数 (口径同 crw/locslice_crw.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.Fold1, 再 python3 locslice_fold1.py <H> [-v]
# 本路没有参数化模块 (Col 是带参数的模块, 经 Col.oO 与 open Col 使用; 切片看不见模块应用, Col 内定义手工列为根).
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def tot(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [('OCF.Lean.'+m,n) for n in ns.split()]
def by_mod(P):
    c=collections.Counter()
    for n in P: c[n[0].replace('OCF.Lean.','')]+=lines(n)
    return ', '.join('%s %d'%kv for kv in c.most_common(40))
# 第 1 层: 定义 (树, 塔, 层号, 世界, 视图的类型)
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊲_ _⊞_')+M('Fold1If','Tw Lv')+
    M('Fold1Fold','Vw'))
# 第 2 层: 折叠, 闭项, FGH
L2=(M('Fold1If','mul topT ΣT top')+M('Fold1Base','Wi liftK frK toK sub updAt')+
    M('Fold1Fold','lgk cmpk extC ext liftS liftL vwC vw ce cw oo oO ΦV Φ')+[('OCF.Lean.Fold1Fold','module Col')]+
    M('Fold1','TΩ num ω′ lg-num lg-ω′ TΩ1 yΩ lg-yΩ TΩΩ iter FGH fghΩ1'))
# 第 3 层: 证书
L3=(M('Fold1Base','LS Lg* lg*⊲ Lg*-⊞ Lg*-mul ls⊥ step* sup* ℓT lgB⊥ up-⊲ Lg*-up ι-⊲ Lg*-ι lg-top* lg-ΣT lgWi lgSub updAt-P')+
    M('Fold1Fold','extLg monoV Φ-mono lgV Φ-lg')+M('Fold1','LgB-TΩ LgB-TΩΩ'))
labs=['定义','+折叠, 闭项, FGH','+证书']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
bad=[n for n in P[3] if not (n[0].startswith('OCF.Lean.Fold1') or n[0]=='OCF.Lean.CRwBase')]
print('层3 闭包里 Fold1*, CRwBase 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
FOLD=M('Fold1Fold','Φ ΦV ce cw oo oO vw vwC liftS liftL extC cmpk lgk')+[('OCF.Lean.Fold1Fold','module Col')]
fs=set(x for m,n in FOLD for x in find(m,n))
print('折叠本身 (Φ, 视图, 坍缩链): %d 行'%sum(lines(n) for n in fs))
WLD=M('Fold1Fold','ext extLg')+M('Fold1Base','sub lgSub liftK frK toK ftK bdDn bdUp prDn lgDn updAt updAt-P')
ws=set(x for m,n in WLD for x in find(m,n))
print('层3 里世界与路径搬运的块: %d 行'%sum(lines(n) for n in ws&P[3]))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['Fold1If','Fold1Base','Fold1Fold','Fold1']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
