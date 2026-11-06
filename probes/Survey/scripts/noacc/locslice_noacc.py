# -*- coding: utf-8 -*-
# NoAcc 一路的分层行数 (改写自 crw/locslice_crw.py; 口径同: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.NoAcc, 再 python3 locslice_noacc.py <H>
# 参数化模块 CRwFold (I), CRwPath (I), NoAccFold (I) 经 `open import ... I₁` 应用; 切片看不见模块应用, 模块内定义手工列为根.
# 两列: 逐点 (NoAcc 的 TXᴾ, 无证书) 与累加 (CRw 的 TX, 形状证书), 同一台切片机, 同一闭项读法 (判断).
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
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊲_ _⊞_')+M('CRwIf','CRwIf')+
    M('CRwFold','Tw XS Bs bS Lev Cl Dc Po PS PH Lt Acc Tg Nd'))
SUP=M('CRwFold','cS cL cl emb frE along frA caseDc pick dcl dcx poΩ poF pX PSX topT ΣT gt topL top wf⊥ g⊥ wfX gX wf ndS ndL mul chain lg↓ ⊏⊑')
INST=M('CRw','Σ₀ leg Lg-leg Lg-Σ₀ I₁ PH-cd PH-ιu PH-Ωc PH-gt PH-topL W₀ iter FGH')
cols={
 'NoAcc TXᴾ (逐点)': (L1, SUP+INST+M('NoAccFold','Φᴾ')+M('NoAcc','TXᴾ fghXᴾ'), []),
 'CRw TX (累加)':    (L1, SUP+INST+M('CRwFold','Σ⁺ Φ')+M('CRw','TX'),
                      M('CRwFold','Sh Sh-⊞ Sh-mul Sh-chain Sh-Σ Sh-case Sh-Φ sh→lg')+M('CRw','LgB-TX')),
}
for name,(r1,r2,r3) in cols.items():
    acc=set(); out=[]
    for i,roots in enumerate([r1,r2,r3],1):
        acc=acc|C(roots) if roots else acc
        out.append(tot(acc))
    print('%s: 层1 %d, 层2 %d, 层3 %d | 记号模块 %d'%(name,out[0],out[1],out[2],note(acc)))
    print('    层3 逐模块:',by_mod(acc))
    bad=[n for n in acc if not (n[0].startswith('OCF.Lean.CRw') or n[0].startswith('OCF.Lean.NoAcc'))]
    print('    闭包里 OCF.Lean.CRw*/NoAcc* 之外的块数:',len(bad))
for m,n in [('NoAccFold','Φᴾ'),('CRwFold','Φ'),('CRwFold','Σ⁺'),('CRwFold','Sh-Σ')]:
    print('  块 %s.%s: %d 行'%(m,n,sum(lines(x) for x in find('OCF.Lean.'+m,n))))
P=C(M('NoAccIf','NoAccIf PtFold'))
print('接口 NoAccIf (含 CRwBase 闭包): %d 行; 本文件: %d 行'%(tot(P),sum(lines(n) for n in P if n[0]=='OCF.Lean.NoAccIf')))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('各文件代码行 (agda 块非空非注释 / 全文):')
for m in ['NoAccIf','NoAccFold','NoAccStuck','NoAccTest','NoAcc']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; k=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): k+=1
    print('  ',m,k,'/',len(t))
