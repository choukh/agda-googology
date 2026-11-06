# -*- coding: utf-8 -*-
# X2 一路的分层行数 (改写自 x1up/locslice_x1up.py, 口径相同: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.X2, 再 python3 locslice_x2.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 X2Fold (V) 经 `open XF I₂` 应用, X1UpFold (U) 经 `open UF IU` 应用, PathOutFold (P) 经 `open PF IX₁` 应用, TySupFold (R) 经 `open F R` 应用;
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'X2'))
def xu(P): return sum(lines(n) for n in P if n[0].startswith(A+'X1Up'))
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
# X1Up 的根 (同 locslice_x1up.py; 闭项 TU 不在内, 本路不用它)
FOLD='LS topU ΣU ClD cS cL clD emb frE along frA pickU decU caseU ΦU ΦX'
PATH=('psStep psSup base PSL PHU PH→g g→PH PH-mono PH-⊞ PH-mul PH-Σ PH-chain '
      'PH-up PH-ι PH-topU PH-ΣU ClP pS pL clP evE upkE evA upkA IH₁ IH₂ PH-ch PH-pk PH-nd PH-ΦU PH-ΦX')
MODS=[(A+'X1UpFold','module StepPS'),(A+'X1UpFold','module SupPS'),(A+'X1UpFold','module Nd')]
XU1=M('X1UpIf','PS PHg X1UpIf')+M('X1UpFold','LS')
XU2=M('X1UpFold',FOLD+' '+PATH)+MODS+M('X1Up','_≼₁_ ev↑₁ adm↓₁ ≼-nxt₁ IU')
XU3=M('X1UpFold','Lg-topU Lg-ΣU')
# 本路
X1=(M('X2If','ClX X2If')+M('X2Inst','ofU X₂ G₂ XS₂ κΩ₂ _⊏tr_ Ev₂ idW CvK₂'))
XFOLD='CB cv ΦB chU caseX Ψ₂'
XPATH='Br PH₂ PH-chU'
IFOLD='clsC cls₂ lfK lfE cvK₂ cvE₂ I₂ gt₂ topL₂ TX2 fghX2'
IPATH=('psBot QS PS₂ PHX LiftOK liftD liftOK PH-cv PH-ι₂ CB-ι CB-⊞ CB-gt PHX-gt PH₂-gt PH₂-top')
X2_=(M('X2Fold',XFOLD+' '+XPATH)+M('X2Inst',IFOLD+' '+IPATH)+[(A+'X2Inst','module Bot₂')])
X3=M('X2Fold','Sh-caseX Sh-Ψ₂')+M('X2Inst','LgB-TX2 gt₂-⊲ Lg-gt₂ Lg-topL₂')
X4=M('X2Inst','comp-Ω comp-0 comp-1 cls-root cls-new cls-base no-ΩΩ')+M('X2','IsLim Head0 head-lim kept no32 shift-kept-not-PH')
labs=['定义 (接口 PathOutIf+X1UpIf+X2If, 层号 X₁/叠层 LS/X₂ 的种类结构 XS₂, 世界与证据, Lv, KS/HB/step/sup)',
      '折叠 (Ψ₂, ΦB, cv, 分类 cls₂, ΦU 与上层路径, Ψ, dec₁, 可数层号 Φ, 地板 topL₂ 与其路径, 闭项, FGH)',
      '证书 (Sh-Ψ₂, Sh-Ψ, LgB-TX2, 地板合法 Lg-topL₂/Lg-topU/Lg-topL)',
      '形状 (comp-*, cls-*, head-lim, no-ΩΩ, shift-kept-not-PH)']
acc=set(); print('== 闭项 TX2 (X₂ 的地板经 Ψ₂ 折到第 0 层)')
for i,(lab,roots) in enumerate(zip(labs,[PO1+XU1+X1,PO2+XU2+X2_,PO3+XU3+X3,X4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | X1Up 承接 %d | PathOut 承接 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),xu(acc),po(acc),tree(acc),note(acc)))
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
# 本路各定义自身的行数 (不取闭包): 折叠, 路径, 证书, 形状
def own(ms): return sum(lines(x) for n in ms for x in find(*n))
grp=[('折叠 (X2Fold: CB cv ΦB chU caseX Ψ₂)',M('X2Fold',XFOLD)),
     ('路径 (X2Fold: Br PH₂ PH-chU)',M('X2Fold',XPATH)),
     ('实例的分类与换层 (X2Inst: clsC cls₂ lfK lfE cvK₂ cvE₂ I₂)',M('X2Inst','clsC cls₂ lfK lfE cvK₂ cvE₂ I₂')),
     ('地板与闭项 (X2Inst: gt₂ topL₂ TX2 fghX2)',M('X2Inst','gt₂ topL₂ TX2 fghX2')),
     ('实例的路径 (X2Inst: '+IPATH+', Bot₂)',M('X2Inst',IPATH)+[(A+'X2Inst','module Bot₂')]),
     ('证书 (X3)',X3),('形状 (X4)',X4),('层 1 的本路定义',[n for n in X1 if n[0].startswith(A+'X2')])]
for lab,ms in grp: print('== 自身行数 %s: %d'%(lab,own(ms)))
