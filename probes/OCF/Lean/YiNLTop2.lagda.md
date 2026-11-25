# 第二塔项的完整 Leaf
验收文件；第 0 步三件俱全：Ω_{Ω+1} 是读法、封顶全部读法、且其 Leaf 成立。
编译定理 `leaf-tw2` 对任意 Rd 推导成立；未实填整个 Cn 的 Leaf。
来源：读回、上下文 Leaf 与封顶分别取 `YiNLRead`、`YiNLRaise`、`YiNLBound2`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLTop2 where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLCheck as LL
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiNLRead
open import OCF.Lean.YiNLCtx
open import OCF.Lean.YiNLCeiling using (κ₂)
open import OCF.Lean.YiCNDomain using (Cn; cn-tw)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiNLRaise

open import OCF.Lean.YiNLBound2 using (Upper₂; upper₂)

LeafTop₂ : Set
LeafTop₂ = GR.R (tw 2) (E.Ωt κ₂) (proj₁ (O.Ωt (tw 2)))

TopCheck₂ : Set
TopCheck₂ = Upper₂ × LeafTop₂

from-top₂ : TopCheck₂ → ∀ {ν} → GR.Rd (tw 2) ν →
  GR.R (tw 2) (E.Ωt ν) (proj₁ (O.Ωt (tw 2)))
from-top₂ (ub , lf) q = LL.rdown (tw 2) (Ωt-mono (ub q)) lf

cn₂ : Cn (tw 2)
cn₂ = cn-tw 2

rd-top₂ : GR.Rd (tw 2) κ₂
rd-top₂ = GR.ca (inj₂ (E.Ωt (E.natT 1) , cof-regular (E.Ωt (E.natT 1)) , LL.rdΩ ,
  λ η c r → subst (GR.Rd (tw 1 ⊕ ↑ (tw 1) c)) (sym (fs-regular (E.Ωt (E.natT 1)) η))
    (GR.rd-add (tw 1) (↑ (tw 1) c) (readR (tw 1) r))))

ChildLeaf₂ : Set
ChildLeaf₂ = ∀ {η} (c : Tr (tw 1)) → GR.R (tw 1) η c →
  GR.R (tw 1 ⊕ ↑ (tw 1) c) (E.Ωt η) (proj₁ (O.Ωt (tw 1 ⊕ ↑ (tw 1) c)))

cof-top₂ : E.cof (E.Ωt κ₂) ≡ E.cΩ (E.Ωt (E.natT 1))
cof-top₂ = refl

fs-top₂ : ∀ η → E.fsT (E.Ωt κ₂) η ≡ E.Ωt η
fs-top₂ η = refl

leaf-from-child₂ : ChildLeaf₂ → LeafTop₂
leaf-from-child₂ ch = H.mΩ cof-top₂ LL.rdΩ
  (λ η c r → subst (λ t → GR.R (tw 2) t
    (up zero c (proj₁ (O.Ωt (tw 1 ⊕ ↑ (tw 1) c))) (proj₂ (O.Ωt (tw 1 ⊕ ↑ (tw 1) c)))))
    (sym (fs-top₂ η)) (H.mU H.mz (ch c r)))
  where open import Data.Product using (proj₂)

child-leaf₂ : ChildLeaf₂
child-leaf₂ {η} c r = raiseR (tw 1) (prefix (tw 1)) [] (GR.c0 refl)
  (LL.rdown (tw 1) (Ωt-mono (inj₁ E.[]<)) LL.leafΩ) r

leaf-top₂ : LeafTop₂
leaf-top₂ = leaf-from-child₂ child-leaf₂


top-check₂ : TopCheck₂
top-check₂ = upper₂ , leaf-top₂

leaf-tw2 : ∀ {ν} → GR.Rd (tw 2) ν → GR.R (tw 2) (E.Ωt ν) (proj₁ (O.Ωt (tw 2)))
leaf-tw2 = from-top₂ top-check₂
```
