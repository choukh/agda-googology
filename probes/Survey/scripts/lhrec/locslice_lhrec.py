# -*- coding: utf-8 -*-
# LHRec 一路的分层行数 (口径同 recb/locslice_recb.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.LHRec, 再 python3 locslice_lhrec.py <H>
# 本路没有折叠与 Cd 上的闭项: 层 2 是 "+ 回灌, 地板, 实例, Λ 的地板", 层 3 是 "+ 合法". 实例 J₁ 的律要 Lg-leg, 所以层 2 已含合法化的证明.
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
def M(m,ns): return [('OCF.Lean.'+m,n) for n in ns.split()]
def by_mod(P):
    c=collections.Counter()
    for n in P: c[n[0].replace('OCF.Lean.','')]+=lines(n)
    return ', '.join('%s %d'%kv for kv in c.most_common(40))
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊞_')+M('LHRecTy','LH Lv FXL IxL')+
    M('LHRecIf','WL LeW LgWL LHRecIf')+M('LHRecLay','lvl node upL _⊕L_ ΩL twL ΛL'))
L2=(M('LHRecLeg','Ctx ek frC toC pw θ θK Σᴸ leg rfL w₀L AdmK J₁')+M('LHRecFl','gcF ixK cxI flL ΣF')+M('LHRec','flΛ'))
L3=(M('LHRecLeg','Lg-leg lw₀L')+M('LHRecFl','Lg-flL')+M('LHRec','Lg-flΛ'))
labs=['定义 (层号, 种类结构, 接口, 层号算术)','+回灌, 地板, 实例, Λ 的地板','+合法']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: %d'%(i,lab,tot(acc)))
    print('    逐模块:',by_mod(acc))
bad=[n for n in P[3] if not (n[0]=='OCF.Lean.CRwBase' or n[0].startswith('OCF.Lean.LHRec'))]
print('层3 闭包里 CRwBase, LHRec* 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
def piece(lab,ms):
    xs=set(x for m,n in ms for x in find(m,n))
    print('  %-40s %d'%(lab,sum(lines(n) for n in xs)))
print('逐件 (块的行数, 不含依赖):')
piece('层号与种类结构 (LH, Lv, FXL, IxL)',M('LHRecTy','LH Lv FXL IxL ixL'))
piece('接口 (WL, LeW, LgWL, LHRecIf)',M('LHRecIf','WL LeW LgWL LHRecIf'))
piece('层号算术 (lvl node upL ⊕L ΩL twL ΛL fixL)',M('LHRecLay','lvl node upL _⊕L_ ΩL twL ΛL fixL'))
piece('上下文 Ctx 与沿上下文的搬运',M('LHRecLeg','Ctx ek frC toC frto pw lgpw bdTo bdFr prFr'))
piece('θ 累加 (新种类) 与单调, 合法',M('LHRecLeg','θ θ-⊲ Lg-θ'))
piece('θK (一切种类) 与单调, 合法',M('LHRecLeg','θK θK-⊲ Lg-θK'))
piece('合法化 leg, Lg-leg',M('LHRecLeg','Σᴸ leg Lg-leg Lg-Σᴸ'))
piece('世界自反, 合法世界, 实例',M('LHRecLeg','rfL w₀L lw₀L AdmK J₁'))
piece('up, ι 保第一位置与合法',M('LHRecFl','up-⊲ Lg-up ι-⊲ Lg-ι'))
piece('地板 flL 与 Lg-flL',M('LHRecFl','gcF ixK cxI flL ΣF Lg-flL Lg-ΣF'))
piece('入口 (flΛ, Lg-flΛ, leg-ok, fl-ok, inst)',M('LHRec','flΛ Lg-flΛ leg-ok fl-ok inst'))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['LHRecTy','LHRecIf','LHRecLeg','LHRecLay','LHRecFl','LHRec']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
