# -*- coding: utf-8 -*-
# CRw 一路的分层行数 (口径同 leant/locslice_leant.py 与 x1up/locslice_x1up.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.CRw, 再 python3 locslice_crw.py <H> [-v]
# 参数化模块 CRwFold (I), CRwPath (I) 经 `open import ... I₁` 应用; 切片看不见模块应用, 模块内定义手工列为根.
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
V='-v' in sys.argv
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊲_ _⊞_')+M('CRwIf','CRwIf')+
    M('CRwFold','Tw XS Bs bS Lev Cl Dc Po PS PH Lt Acc Tg Nd')+M('CRwPath','psStep psSup PSL'))
# 第 2 层: 闭项与 FGH. TU 要路径作跨底折叠的参数 (PH-inU), 对角 yU 要 LgB-TU (同 X1Up 的口径), 所以路径与部分证书在这层.
L2=(M('CRwFold','cS cL cl emb frE along frA caseDc pick dcl dcx poΩ poF pX PSX topT ΣT gt topL top wf⊥ g⊥ wfX gX wf ndS ndL mul chain Σ⁺ lg↓ ⊏⊑ Φ')+
    M('CRwPath','PH-mono PH-⊞ PH-mul PH-Σ PH-chain PH-up PH-ι PH-top PH-ΣT ClP pS pL clP evE upkE evA upkA IH₁ IH₂ Kc Sc Ac PH-ch PH-pk PH-nd PH-ΦX')+
    M('CRw','Σ₀ leg Lg-leg Lg-Σ₀ I₁ PH-cd PH-ιu PH-Ωc PH-gt PH-topL W₀ TX inU PH-inU TU TU1 yU lg-yU TU2 iter FGH fghX'))
L3=(M('CRwFold','Sh Sh-⊞ Sh-mul Sh-chain Sh-Σ Sh-case Sh-Φ sh→lg')+M('CRw','LgB-TX LgB-TU LgB-TU2'))
labs=['定义','+折叠, 实例, 闭项, FGH','+证书']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
bad=[n for n in P[3] if not n[0].startswith('OCF.Lean.CRw')]
print('层3 闭包里 OCF.Lean.CRw* 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
# 路径专用 (只为闭项 TU 的跨底输入带路径): CRwPath 全部 + CRw 的地板路径 + Fold 里的 PS/PH/PSX/Nd/nd*
PATH=(M('CRwPath','psStep psSup PSL PH-mono PH-⊞ PH-mul PH-Σ PH-chain PH-up PH-ι PH-top PH-ΣT ClP pS pL clP evE upkE evA upkA IH₁ IH₂ Kc Sc Ac PH-ch PH-pk PH-nd PH-ΦX')+
      M('CRwFold','PS PH PSX Nd ndS ndL')+M('CRw','PH-cd PH-ιu PH-Ωc PH-gt PH-topL PH-inU'))
ps=set(x for m,n in PATH for x in find(m,n))
print('层3 里路径专用的块: %d 行; 其余 %d 行'%(sum(lines(n) for n in ps&P[3]), tot(P[3])-sum(lines(n) for n in ps&P[3])))
FOLD=M('CRwFold','Φ caseDc pick dcl dcx mul chain Σ⁺ lg↓ ⊏⊑')
fs=set(x for m,n in FOLD for x in find(m,n))
print('折叠本身 (Φ, 决定, 累加): %d 行'%sum(lines(n) for n in fs))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['CRwBase','CRwIf','CRwFold','CRwPath','CRw','CRwCmp']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
