# -*- coding: utf-8 -*-
# X1Up 一路的分层行数 (口径同 pathout/locslice_pathout.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.X1Up, 再 python3 locslice_x1up.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 X1UpFold (U) 经 `open UF IU` 应用, PathOutFold (P) 经 `open PF IX₁` 应用, TySupFold (R) 经 `open F R` 应用;
# 切片看不见模块应用, 模块内定义手工列为根 (近似, 同 pathout 的做法).
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'X1Up'))
def po(P): return sum(lines(n) for n in P if n[0].startswith(A+'PathOut'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
# PathOut 的根 (同 locslice_pathout.py), 闭项 TXL 换成本路的
PO1=(M('PathOutIf','DcP OkP PathOutIf')+
    M('PathOutX1','X₁ XS₁ κΩ one LgW₁ Ev₁ Adm₁ nxt₁ Tg₁ lvX₁')+
    M('TySupIf','AccR Dc TySupIf')+
    M('TySupC','Cd ofC LC _⊑ᶜ_ _⊏ᶜ_ lvC posC toC')+
    M('TySupSum','topΣ ΣΩ')+
    M('LFReTy','S⊥ Lv LH')+
    M('HtTowerTy','KS HB _⊲[_]_ step up _⊞_ sup ι LgB'))
PO2=(M('PathOutFold','PH caseP Ψ')+
    M('PathOutX1','Σ₀ leg shift₁ unsuc pickΩ conv posB dec₁')+
    M('TySupFold','mul chain Σ⁺ caseDc Φ')+
    M('TySupC','wfC goC ⊏→⊑ᶜ lgC↓ᶜ along frA pick decC noKC')+
    M('TySupSum','ICdΣ')+
    M('HtTowerTy','cmpB ⊲ᴮ-tr lgB⊲ z⊲ᴮ ⊞-fst')+
    M('PathOut','gt topL W₀')+
    M('TySup','ord⊥'))
PO3=(M('PathOutFold','Sh-caseP Sh-Ψ')+
    M('PathOutX1','Lg-leg Lg-Σ₀ lg-nxt₁ tg-nxt₁ adm-shift₁ okΩ okI correct₁ IX₁')+
    M('TySupFold','Sh Sh-⊞ Sh-mul Sh-mulL Sh-chain Sh-Σ Sh-case Sh-Φ')+
    M('TySupSum','Lg-topΣ Lg-ΣΩ')+
    M('PathOut','gt-⊲ Lg-gt Lg-topL PH-⊞ι PH-gt PH-topL lW₀ sh→lgB₁'))
# 本路
FOLD='LS topU ΣU ClD cS cL clD emb frE along frA pickU decU caseU ΦU ΦX'
PATH=('psStep psSup base PSL PHU PH→g g→PH PH-mono PH-⊞ PH-mul PH-Σ PH-chain '
      'PH-up PH-ι PH-topU PH-ΣU ClP pS pL clP evE upkE evA upkA IH₁ IH₂ PH-ch PH-pk PH-nd PH-ΦU PH-ΦX')
L1=PO1+M('X1UpIf','PS PHg X1UpIf')+M('X1UpFold','LS')
MODS=[(A+'X1UpFold','module StepPS'),(A+'X1UpFold','module SupPS'),(A+'X1UpFold','module Nd')]
def L2(top): return PO2+M('X1UpFold',FOLD+' '+PATH)+MODS+M('X1Up','_≼₁_ ev↑₁ adm↓₁ ≼-nxt₁ IU TU '+top)
def L3(top): return PO3+M('X1UpFold','Lg-topU Lg-ΣU')+M('X1Up','LgB-TU '+top)
L4=M('X1Up','OkU okP okU RootΩ₁ HeadΩ₁ nonflat1')
labs=['定义 (接口 PathOutIf+X1UpIf, 层号 X₁ 与叠层 LS, 世界与证据, Lv, KS/HB/step/sup)',
      '折叠 (ΦU, decU, 上层路径 PSL 与 PH-ΦU, Ψ, dec₁, shift₁, 可数层号 Φ, 实例 IU, 闭项, FGH)',
      '证书 (Sh-Ψ, LgB-TU, 地板合法 Lg-topU/Lg-topL)',
      '形状 (okU 决定正确, nonflat1)']
for nm,t2,t3 in [('TU1 (X₁⊕1, 读 ψ₀(Ω_{Ω₁+1}))','TU1 fghU1','LgB-TU'),
                 ('TU2 (对角, 读 ψ₀(Ω_{Ω₁·2}))','TU2 yU fghU2','LgB-TU2')]:
    acc=set(); print('== 闭项',nm)
    for i,(lab,roots) in enumerate(zip(labs,[L1,L2(t2),L3(t3),L4]),1):
        acc=acc|C(roots)
        print('  层%d %s: 本路新增 %d | PathOut 承接 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),po(acc),tree(acc),note(acc)))
        if '-v' in sys.argv:
            c=collections.Counter()
            for n in acc: c[n[0].replace(A,'')]+=lines(n)
            print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
# 本路层 2 里, 折叠本身与路径机制各多少 (各自的闭包限制在 X1UpFold)
f=C(M('X1UpFold',FOLD)); p=C(M('X1UpFold',PATH)+MODS)
print('== X1UpFold 分项: 折叠 (闭包) %d 行; 路径机制 (闭包, 含折叠) %d 行; 路径独有 %d 行'%(
    sum(lines(n) for n in f if n[0]==A+'X1UpFold'), sum(lines(n) for n in p if n[0]==A+'X1UpFold'),
    sum(lines(n) for n in p-f if n[0]==A+'X1UpFold')))
