# -*- coding: utf-8 -*-
# PathOut 一路的分层行数 (同 fab3/locslice_fab3.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.PathOut, 再 python3 locslice_pathout.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 PathOutFold (P) 经 `open PF IX₁` 应用, TySupFold (R) 经 PathOutFold 内的 `open F R` 应用, 切片看不见模块应用, 模块内定义手工列为根 (近似).
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'PathOut'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('PathOutIf','DcP OkP PathOutIf')+
    M('PathOutX1','X₁ XS₁ κΩ one LgW₁ Ev₁ Adm₁ nxt₁ Tg₁ lvX₁')+
    M('TySupIf','AccR Dc TySupIf')+
    M('TySupC','Cd ofC LC _⊑ᶜ_ _⊏ᶜ_ lvC posC toC')+
    M('TySupSum','topΣ ΣΩ')+
    M('LFReTy','S⊥ Lv LH')+
    M('HtTowerTy','KS HB _⊲[_]_ step up _⊞_ sup ι LgB'))
L2=(M('PathOutFold','PH caseP Ψ')+
    M('PathOutX1','Σ₀ leg shift₁ unsuc pickΩ conv posB dec₁')+
    M('TySupFold','mul chain Σ⁺ caseDc Φ')+
    M('TySupC','wfC goC ⊏→⊑ᶜ lgC↓ᶜ along frA pick decC noKC')+
    M('TySupSum','ICdΣ')+
    M('HtTowerTy','cmpB ⊲ᴮ-tr lgB⊲ z⊲ᴮ ⊞-fst')+
    M('PathOut','gt topL W₀ TXL fghXL')+
    M('TySup','ord⊥'))
L3=(M('PathOutFold','Sh-caseP Sh-Ψ')+
    M('PathOutX1','Lg-leg Lg-Σ₀ lg-nxt₁ tg-nxt₁ adm-shift₁ okΩ okI correct₁ IX₁')+
    M('TySupFold','Sh Sh-⊞ Sh-mul Sh-mulL Sh-chain Sh-Σ Sh-case Sh-Φ')+
    M('TySupSum','Lg-topΣ Lg-ΣΩ')+
    M('PathOut','gt-⊲ Lg-gt Lg-topL PH-⊞ι PH-gt PH-topL lW₀ sh→lgB₁ LgB-TXL'))
L4=(M('PathOut','dec-root'))
acc=set(); print('== 无条件闭项 TXL (lΩ 层号 X₁ 的合法地板, 带路径的带类型折叠 PathOutFold.Ψ)')
labs=['定义 (接口, 层号, 世界与证据, Lv, KS/HB/step/sup)','折叠 (Ψ, 决定 dec₁ 含 cmpB, 带路径的回灌 shift₁, 可数层号的 Φ, 闭项, FGH)','证书 (Sh-Ψ, 地板合法 Lg-topL, 地板的路径 PH-topL, LgB-TXL)','形状 (dec-root)']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
