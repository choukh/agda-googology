#!/usr/bin/env python3
"""由 OrdLabZ*, OrdLabB* 生成 EmbVVOZ*, EmbVVB*: 改用 Sb 更大的 NF₁ 与去头的树. 其余逐字."""
import re,os,sys
root=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','OCF','Align')
rd=lambda n: open(os.path.join(root,n+'.lagda.md'),encoding='utf8').read()
def wr(n,s): open(os.path.join(root,n+'.lagda.md'),'w',encoding='utf8').write(s)
OZ='Decouple DecoupleBase GoodLBase OmegaExpBase OmegaSqBase Prefix Relative Stage2Label Uniform3 Uniform3Base Uniform3Depth1 Uniform3Depth2Class Uniform3Depth2Fold Uniform3Depth2W Uniform3Full Uniform3Hon Uniform3Rel Uniform3SqA Uniform3SqABase Uniform4Base Uniform4Head Uniform5Class Uniform5Close Uniform5Eval Uniform5Head Uniform5Psi Uniform5Tr UniformS'.split()
LZ=os.environ.get('LZ','').split()   # 需要克隆的 LadderLabZ 模块
def rn(s):
    s=re.sub(r'OCF\.Align\.OrdLabZ('+'|'.join(OZ)+r')\b',r'OCF.Align.EmbVVOZ\1',s)
    s=s.replace('OCF.Align.LadderLabZStandardOmega','OCF.Align.EmbVVLZStandardOmega')
    for m in LZ:
        s=re.sub(r'OCF\.Align\.LadderLabZ'+m+r'\b','OCF.Align.EmbVVLZ'+m,s)
    return s
def body(n):
    s=rd(n); i=s.index('```agda'); return s[i:]
for m in OZ:
    wr('EmbVVOZ'+m,'> **机械克隆, 验收用.** 由 `OrdLabZ%s` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).\n\n'%m+rn(body('OrdLabZ'+m)))
for m in LZ:
    wr('EmbVVLZ'+m,'> **机械克隆, 验收用.** 由 `LadderLabZ%s` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入. 入口 [EmbVV](EmbVV.lagda.md).\n\n'%m+rn(body('LadderLabZ'+m)))
B='Base Class Rel Psi Eval'.split()
def rb(s):
    s=rn(s)
    s=re.sub(r'OCF\.Align\.OrdLabB('+'|'.join(B)+r')\b',r'OCF.Align.EmbVVB\1',s)
    s=s.replace('open import OCF.Align.LadderOrdTree 𝕊','open import OCF.Align.EmbVVTree 𝕊 dr')
    s=s.replace('(𝕊 : HtB) (𝕏 : PxB 𝕊) where','(𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) (𝕏 : PxB 𝕊 dr) where')
    s=s.replace('𝕊 𝕏','𝕊 dr 𝕏')
    return s
# Base
s=rb(body('OrdLabBBase'))
s=s.replace('open import OCF.Align.LadderOrdBase\n','open import OCF.Align.LadderOrdBase\nimport OCF.Align.EmbVVMode\n',1)
s=s.replace('module _ (𝕊 : HtB) where','module _ (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where\n  open OCF.Align.EmbVVMode 𝕊 using (HdM; keep; drop; repl)')
a=s.index('  data Row₀'); b=s.index('  record PxB')
s=s[:a]+'''  data Row₀ (P : Ht → T → T) : (m : Ht) → View _<ᴸ_ h₀ m → HdM m → Set where
    rb : ∀ {b} → P h₀ [] ≡ Ω₁ ∷ [] → Row₀ P h₀ base b
    rc : ∀ {m n b} (q : n <ᴸ m) → cof (P m []) ≡ cΩ [] → (∀ θ → fsT (P m []) θ ≡ P n θ) → Row₀ P m (clos q) b
    rl : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs) keep
    rh : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → (∀ i → fsn (P m []) i ≡ P (F i) []) → Row₀ P m (chain F qs) drop
    rr : ∀ {m n} (q : n <ᴸ m) (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ P n [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs) (repl n q)

'''+s[b:]
s=s.replace('P-row   : ∀ m → Row₀ P m (view m)','P-row   : ∀ m → Row₀ P m (view m) (dr m)')
wr('EmbVVBBase','> **机械改写, 验收用.** 由 `OrdLabBBase` 经 `Survey/scripts/embvv/mk_world.py`: `Row₀` 多一种去头的链行 `rh`. 入口 [EmbVV](EmbVV.lagda.md).\n\n'+s)
# Class
s=rb(body('OrdLabBClass'))
s=s.replace('open import OCF.Align.LadderOrdBase\n','open import OCF.Align.LadderOrdBase\nimport OCF.Align.EmbVVMode\n',1)
s=s.replace('(v : View _<ᴸ_ h₀ m) → Row₀ 𝕊 P m v → ∀ mo → Lq m zero true mo (rowV m (ΩI m) v) (Ωt (P m []))','(v : View _<ᴸ_ h₀ m) → Row₀ 𝕊 dr P m v (dr m) → ∀ mo → Lq m zero true mo (rowV m (ΩI m) v) (Ωt (P m []))')
a=s.index('rowLq m I (chain F qs₁) (rl .F .qs₁ cc f0 fs) mo ='); b=s.index('FLq : ∀ m →')
ch=s[a:b]
s=s[:a]+'''rowLq m I (chain F qs₁) r mo with dr m | r
rowLq m I (chain F qs₁) r mo | keep | rl .F .qs₁ cc f0 fs =
'''+ch[ch.index('  ll {ps = []}'):ch.index('  where\n')]+'''  where
  𝟏-lab : ∀ mo → Lq m zero true mo (𝟏L {m}) (Ωt [])
  𝟏-lab mo = lwk (ls {ps = []} {y = 𝟏} {ys = []} refl (fl mo) (λ i q ()) (λ ()) lz)
    where
    fl : ∀ mo → FlU mo fz []
    fl hon ()
    fl (wkm c) ()
rowLq m I (chain F qs₁) r mo | repl n q | rr .q .F .qs₁ cc f0 fs =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ { zero → rq (sym (trans (fsn-Ωt (P m []) cc 0) (cong Ωt f0)))
             (subst (λ X → Lq m zero true mo (stepL q X) (Ωt (P n []))) (sym (ΩI≡ q))
                (lwk (Lq-ι↓ q (I q Ord₊.zero hz (l0 refl z≅) n[] z≅ mo))))
        ; (suc i) → rq (sym (trans (fsn-Ωt (P m []) cc (suc i)) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))) })
rowLq m I (chain F qs₁) r mo | drop | rh .F .qs₁ cc fs =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ i → rq (sym (trans (fsn-Ωt (P m []) cc i) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))))

'''+s[b:]
wr('EmbVVBClass','> **机械改写, 验收用.** 由 `OrdLabBClass` 经 `Survey/scripts/embvv/mk_world.py`: 第 0 行多一种去头的链行. 入口 [EmbVV](EmbVV.lagda.md).\n\n'+s)
# Rel
s=rb(body('OrdLabBRel'))
s=s.replace('open import OCF.Align.LadderOrdBase\n','open import OCF.Align.LadderOrdBase\nimport OCF.Align.EmbVVMode\n',1)
s=s.replace('''R-row m I (chain F qs₁) = rl (R-rowL F qs₁ I)
''','''R-row m I (chain F qs₁) = R-rowD (dr m)
  where
  R-rowD : (b : HdM m) → Rq m zero zero (ql (rowD F qs₁ (ΩI m) b)) (ql (rowD F qs₁ (ΩI m) b))
  R-rowD keep = rl (R-rowL F qs₁ I)
  R-rowD drop = rl (λ i → R-rowL F qs₁ I (suc i))
  R-rowD (repl n q) = rl (λ { zero → subst (λ X → Rq m zero zero (stepL q X) (stepL q X)) (sym (ΩI≡ q)) (R-stepL q (I q)) ; (suc i) → R-rowL F qs₁ I (suc i) })
''')
wr('EmbVVBRel','> **机械改写, 验收用.** 由 `OrdLabBRel` 经 `Survey/scripts/embvv/mk_world.py`. 入口 [EmbVV](EmbVV.lagda.md).\n\n'+s)
for m in ['Psi','Eval']:
    s=rb(body('OrdLabB'+m))
    s=s.replace('open import OCF.Align.LadderOrdBase\n','open import OCF.Align.LadderOrdBase\nimport OCF.Align.EmbVVMode\n',1)
    wr('EmbVVB'+m,'> **机械改写, 验收用.** 由 `OrdLabB%s` 经 `Survey/scripts/embvv/mk_world.py`. 入口 [EmbVV](EmbVV.lagda.md).\n\n'%m+s)

# ---- 带 NF₁ 的小定义, 逐字搬到新的 NF₁ 上 ----
def cut(n,a,b):
    s=rd(n); i=s.index(a); j=s.index(b,i); return s[i:j]
ex='''> **机械克隆, 验收用.** 把 `LadderLabZGoodLBase`, `LadderLabZDecoupleBase`, `LadderLabZPrefix` 里类型提到 `NF₁` 的几个定义搬到新的 `NF₁` 上, 代码逐字. `Survey/scripts/embvv/mk_world.py`. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVLZExtra where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
import OCF.Align.EBO as E
open E using (T; PT; c0; c1; cω; cΩ; cof; cofA; cofψ0; cofψ₊; fsn; fsT; cmpᵀ; lt; eq; gt; sucT; Ωt; natT; _<ᵀ_; hd<; tl<; lv<; ar<; []<) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; rep<)
open import OCF.Align.Stage2 using (ctx)
open import OCF.Align.Symbolic using (X₂ᵗ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; Ctbl-pred; []≤) renaming (d₀ to d₀ᴰ)
open import OCF.Align.Closure using (lt→<ᴾ; eq→≡ᴾ; <ᵀ-trans)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.LadderLabZGoodLBase using (ctbl-hd; ctbl-one)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; n[]; n∷; nψ; NF₁-fsn; fsT-mono₁; γ-mono₁; γ′-NF; diag₁-desc-NF; walkD; Vis₁; vh; vd; vs; vt)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; γP)
open import OCF.Align.LadderLabZPrefix using (toX₂)

'''+cut('LadderLabZGoodLBase','fs-mono₁ : ∀ {u}','```\n\n\n**带标签的项都可数')+'''
'''+cut('LadderLabZGoodLBase','Ctbl-ω : ∀ {u}','Lab→Ctbl : ∀').replace('\n\n','\n')+'''
'''+cut('LadderLabZSystemOmega','tailVis : ','occ-tailNF :')+cut('LadderLabZSystemOmega','occVis : ','Occ-NF :')+'''
'''+cut('LadderLabZSystemOmega','tl<₁ : ','occ< : ∀')+cut('LadderLabZSystemOmega','occ< : ∀','```',)+'''
nf1 : NF₁ (natT 1)
nf1 = γ′-NF 0

'''+cut('LadderLabZDecoupleBase','nfγ : ∀ {y ys}','```\n\n\n**链的三个主体')+'''
X₂-NF : NF₁ X₂ᵗ
X₂-NF = diag₁-desc-NF (walkD d₀ᴰ toX₂ (refl , refl , refl , refl , refl , refl , tt))
```
'''
wr('EmbVVLZExtra',ex)
def fix(n):
    p=os.path.join(root,n+'.lagda.md'); s=open(p,encoding='utf8').read()
    s=re.sub(r'(open import OCF\.Align\.LadderLabZSystemOmega using \([^)]*?); occ<\)',r'\1)\nopen import OCF.Align.EmbVVLZExtra using (occ<)',s)
    s=s.replace('using (η₁; cur-holds; occ<; Occ; oh; od; ot)','using (η₁; cur-holds; Occ; oh; od; ot)\nopen import OCF.Align.EmbVVLZExtra using (occ<)')
    s=s.replace('open import OCF.Align.LadderLabZGoodLBase public using (Ctbl-c1; Ctbl-ω; ctbl-hd; ctbl-one; fs-monoA; fs-monoL; fs-mono₁; nf1)','open import OCF.Align.LadderLabZGoodLBase public using (Ctbl-c1; ctbl-hd; ctbl-one)\nopen import OCF.Align.EmbVVLZExtra public using (Ctbl-ω; fs-monoA; fs-monoL; fs-mono₁; nf1)')
    s=s.replace('open import OCF.Align.LadderLabZDecoupleBase public using (1<ctx; ctx1; nfγ; nfω; penT; ΩΩ; γP; ψ₁Ω)','open import OCF.Align.LadderLabZDecoupleBase public using (1<ctx; ctx1; penT; ΩΩ; γP; ψ₁Ω)\nopen import OCF.Align.EmbVVLZExtra public using (nfγ; nfω)')
    s=s.replace('open import OCF.Align.LadderLabZPrefix public using (H1-cmp; H1-fsT; H1-pen; X₂-NF; toX₂)','open import OCF.Align.LadderLabZPrefix public using (H1-cmp; H1-fsT; H1-pen; toX₂)\nopen import OCF.Align.EmbVVLZExtra public using (X₂-NF)')
    open(p,'w',encoding='utf8').write(s)
for m in OZ: fix('EmbVVOZ'+m)

# 遗忘标签
s=rn(body('OrdLabForget'))
wr('EmbVVForget','> **机械克隆, 验收用.** 由 `OrdLabForget` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入. 入口 [EmbVV](EmbVV.lagda.md).\n\n'+s.replace('OCF.Align.OrdLabForget','OCF.Align.EmbVVForget'))
