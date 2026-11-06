# -*- coding: utf-8 -*-
# RecB 一路的分层行数 (口径同 crw/locslice_crw.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.RecB, 再 python3 locslice_recb.py <H> [-v]
# 参数化模块 CRwFold (I), CRwPath (I), RecBFold (J), RecBPath (J) 经模块应用使用; 切片看不见模块应用, 用到的模块内定义手工列为根.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
# CRw 的根 open 了 `Thm PH-topL using (PH-ΦX)` 与 `Top PH-topL using (PH-top)` (只为 CRw 自己的闭项);
# 切片从任一 CRw 块经根跟到这些 open, 会把 CRw 的折叠 Φ 与 CRwPath 全部拖进来. RecB 只用 CRw 的 I₁, leg, FGH,
# 它们不依赖这些 open, 所以这里对 OCF.Lean.CRw 不跟随根的 open (其余模块照常).
_succ=succ
def succ(node):
    out=_succ(node)
    if node[0]!='OCF.Lean.CRw': return out
    f=chunk('OCF.Lean.CRw'); op=set(f.chunks[f.rootc].get('opens',[]))
    return [t for t in out if not (t[0]=='OCF.Lean.CRw' and t[1] in op)]
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
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊲_ _⊞_')+M('CRwIf','CRwIf')+M('RecBIf','RecBIf')+
    M('CRwFold','Tw Cl Dc Po PS PH')+M('CRwPath','psStep psSup')+
    M('RecBFold','Ix FX XSof Sb ιK AccC')+M('RecBPath','PSL triv FQ lift'))
L2=(M('CRwFold','cS cL cl emb frE along frA caseDc pick dcl poΩ poF topT ΣT mul chain Σ⁺ lg↓ ⊏⊑')+
    M('CRwPath','PH-mono PH-⊞ PH-mul PH-Σ PH-chain PH-up PH-ι')+
    M('CRw','Σ₀ leg Lg-leg Lg-Σ₀ I₁ iter FGH')+
    M('RecBFold','fl gtX top pX PSX dcx dcI wfC gC ΦS ΦX')+
    M('RecBPath','ClP pS pL clP evE upkE evA upkA PH-top PH-ΣT IH₁ IH₂ Kc Sc Ac PH-ch PH-pk PH-nd PH-ΦS ch pk′ nd′ PH-ΦX↓')+
    M('RecB','J₁ PH-cp PH-gtX PH-fl PH-gtL Ok Qn okOwn liftE QL Gd ↓Gd desc inp every gd-inp TN yN lg-yN TD zω Tω fghω'))
L3=(M('CRwFold','Sh Sh-⊞ Sh-mul Sh-chain Sh-Σ Sh-case sh→lg')+M('RecBFold','Sh-ΦS Sh-ΦX')+
    M('RecB','Sh-desc LgB-TN LgB-TD lg-zω LgB-Tω'))
labs=['定义','+折叠, 实例, 闭项, FGH','+证书']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
bad=[n for n in P[3] if not (n[0].startswith('OCF.Lean.CRw') or n[0].startswith('OCF.Lean.RecB'))]
print('层3 闭包里 OCF.Lean.CRw*, RecB* 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
new=set(n for n in P[3] if n[0].startswith('OCF.Lean.RecB'))
print('层3 里 RecB* 新写的块: %d 行; 沿用 CRw* 的块: %d 行'%(sum(lines(n) for n in new), tot(P[3])-sum(lines(n) for n in new)))
PATH=(M('CRwPath','psStep psSup PH-mono PH-⊞ PH-mul PH-Σ PH-chain PH-up PH-ι')+M('CRwFold','PS PH')+
      M('RecBPath','PSL triv FQ lift ClP pS pL clP evE upkE evA upkA PH-top PH-ΣT IH₁ IH₂ Kc Sc Ac PH-ch PH-pk PH-nd PH-ΦS ch pk′ nd′ PH-ΦX↓')+
      M('RecBFold','PSX')+M('RecB','PH-cp PH-gtX PH-fl PH-gtL Ok Qn okOwn liftE QL Gd ↓Gd every gd-inp'))
ps=set(x for m,n in PATH for x in find(m,n))
print('层3 里路径与世界塔专用的块: %d 行; 其余 %d 行'%(sum(lines(n) for n in ps&P[3]), tot(P[3])-sum(lines(n) for n in ps&P[3])))
FOLD=M('RecBFold','ΦS ΦX dcx dcI wfC gC')+M('CRwFold','caseDc pick dcl mul chain Σ⁺ lg↓ ⊏⊑')
fs=set(x for m,n in FOLD for x in find(m,n))
print('折叠本身 (ΦS, ΦX, 决定, 累加): %d 行'%sum(lines(n) for n in fs))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['RecBIf','RecBFold','RecBPath','RecB']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
