# -*- coding: utf-8 -*-
# Fab6 一路的分层行数 (口径同 crw/locslice_crw.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.Fab6, 再 python3 locslice_fab6.py <H> [-v]
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
L1=(M('Fab6Base','KS XK HB _⊲[_]_ LgB step sup up ι S⊥ X⊥ Cd _⊲_ _⊞_')+
    M('Fab6Fold','Tw Cl Dc Acc')+M('Fab6','X₁'))
L2=(M('Fab6Fold','cS cL cl emb frE along frA caseDc pick dcl topT ΣT wf g⊲ mul chain Σ⁺ lg↓ ⊏⊑ Φ')+
    M('Fab6','Σ₀ leg Lg-leg Lg-Σ₀ topL brX nodeX ΦX W₀ TX inU TU TU1 yU lg-yU TU2 iter FGH fghX'))
L3=(M('Fab6Fold','Sh Sh-⊞ Sh-mul Sh-chain Sh-Σ Sh-case Sh-Φ sh→lg')+M('Fab6','Sh-brX Sh-nodeX Sh-ΦX LgB-TX LgB-TU LgB-TU2'))
labs=['定义','+折叠, 闭项, FGH','+证书']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
bad=[n for n in P[3] if not n[0].startswith('OCF.Lean.Fab6')]
print('层3 闭包里 OCF.Lean.Fab6* 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
FOLD=M('Fab6Fold','Φ caseDc pick dcl mul chain Σ⁺ lg↓ ⊏⊑')+M('Fab6','brX nodeX ΦX')
fs=set(x for m,n in FOLD for x in find(m,n))
print('折叠本身 (Φ, ΦX, 决定, 累加): %d 行'%sum(lines(n) for n in fs))
XB=M('Fab6Base','XK')+M('Fab6','X₁ topL brX nodeX ΦX Sh-brX Sh-nodeX Sh-ΦX')
xs=set(x for m,n in XB for x in find(m,n))
print('外部种类与跨底折叠 (XK, X₁, topL, brX, nodeX, ΦX, 其 Sh): %d 行'%sum(lines(n) for n in xs&P[3]))
# 层的代数 (Fab6Lay): 主闭项 TΩ^Ω, 对一切层一条闭项定义. 第 1 层另加 FL 与各层的结构, 不含入口的 ΦX 一路.
print('--- 层的代数 (Fab6Lay, 主闭项 TΩ^Ω; 不含入口的 X₁/ΦX 一路) ---')
K1=(M('Fab6Base','KS XK HB _⊲[_]_ LgB step sup up ι S⊥ X⊥ Cd _⊲_ _⊞_')+M('Fab6Fold','Tw Cl Dc Acc')+
    M('Fab6Lay','S₁ Ω₁ FL extX supX diagX'))
K2=(M('Fab6Fold','cS cL cl emb frE along frA caseDc pick dcl topT ΣT wf g⊲ mul chain Σ⁺ lg↓ ⊏⊑ Φ')+
    M('Fab6','Σ₀ leg Lg-leg Lg-Σ₀ iter FGH')+
    M('Fab6Lay','embT Ψg L₀ ext ιX supL diag clL fgh It pow P Pc one T₀ fghΩ^Ω'))
K3=(M('Fab6Fold','Sh Sh-⊞ Sh-mul Sh-chain Sh-Σ Sh-case Sh-Φ sh→lg')+M('Fab6Lay','Lg-clL Lg-TΩ^Ω'))
acc=set(); Q={}
for i,(lab,roots) in enumerate(zip(['定义','+折叠, 层的算子, 闭项, FGH','+证书'],[K1,K2,K3]),1):
    acc=acc|C(roots); Q[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
ls_=set(x for m,n in M('Fab6Lay','S₁ Ω₁ FL extX supX diagX embT Ψg L₀ ext ιX supL diag clL It pow P Pc') for x in find(m,n))
print('层的代数本身 (FL, ext, supL, diag, Ψg, clL, It, pow, P, Pc): %d 行'%sum(lines(n) for n in ls_&Q[3]))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['Fab6Base','Fab6Fold','Fab6','Fab6Lay','Fab6Cmp']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
