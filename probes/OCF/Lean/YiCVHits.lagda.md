# 真实命中对子域的 Evidence（验收文件）
编译定理：两张表各自终点的 tw 2 零对零请求可直接实填 Evidence，但不满足原 Covers。
tw 1 的另一个真实请求扩为两孩子结点后，补等号得到 Evidence；两张表的非零对角仍为 nothing。
来源：实际命中见证直接复用 YiMTHit；不把补出的等号算作表条目，也不把有限子域当全执行域。
本文件不含序数值或强度结论；表空缺不推出记号依赖。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCVHits where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiMTHit as Hit
open import OCF.Lean.YiCVDomain

actual-zero-pair : Hit.HitΛ Hit.PΛ2ᶻ
actual-zero-pair = Hit.hit-Λ2ᶻ

actual-two-pair : Hit.HitΛ Hit.PΛ1ᶻ
actual-two-pair = Hit.hit-Λ1ᶻ

HitΛᵗ : Hit.Site → Set
HitΛᵗ P = Hit.Hit P Λ Ok-Λ CW.rbΛ (F.B₀ Λ) (λ _ _ → ⊥) zero (z≤ Λ) (O.Ωt zero) ⊥ (proj₁ (O.Ωt Λ))

actual-zero-pairᵗ : HitΛᵗ Hit.PΛ2ᶻ
actual-zero-pairᵗ = 2 , (0 , inj₁ (0 , inj₂ (refl , refl , refl , refl , Hit.is₁ self)))

actual-two-pairᵗ : HitΛᵗ Hit.PΛ1ᶻ
actual-two-pairᵗ = 1 , (1 , inj₁ (0 , (0 , (0 , inj₂
  (refl , refl , refl , refl , Hit.is₂ (lift zero (↑ zero (proj₁ (O.next⁺ (O.next⁺ (O.Ωt zero)))))))))))

data Table : Set where
  minimal keel : Table

data Present {A : Set} : Maybe A → Set where
  present : (a : A) → Present (just a)

single : Nodes
single = record
  { Node = ⊤
  ; Child = λ _ → ⊤
  ; label = λ _ _ → CW.hᵗ 1 zero }

single-table : Table → Maybe ((CW.hᵗ 1 zero ≤ CW.hᵗ 1 zero) Data.Sum.Base.⊎
                              (CW.hᵗ 1 zero ≤ CW.hᵗ 1 zero))
single-table minimal = proj₁ (MT.rbᶻ (tw 2)) zero zero
single-table keel = proj₁ (CW.rbᵗ 2) zero zero

single-present : ∀ t → Present (single-table t)
single-present minimal = present (inj₁ self)
single-present keel = present (inj₁ self)

single-evidence : ∀ t → Evidence (Scope single)
single-evidence t = record
  { E = λ x y → (CW.hᵗ 1 zero ≡ x) × (CW.hᵗ 1 zero ≡ y) × Present (single-table t)
  ; answer = λ { _ _ (refl , refl , _) → inj₂ (inj₁ refl) }
  ; provide = λ { _ _ (tt , tt , tt , ex , ey) → ex , ey , single-present t } }

single-scope : Scope single (CW.hᵗ 1 zero) (CW.hᵗ 1 zero)
single-scope = tt , tt , tt , refl , refl

no-single-cover : Covers single → ⊥
no-single-cover cover with cover zero zero
... | tt , tt , tt , () , ey

real-child : Bool → Tr zero
real-child false = zero
real-child true = proj₁ (O.next⁺ (O.next⁺ (O.Ωt zero)))

real-label : Bool → L
real-label c = CW.hᵗ 0 (real-child c)

real-nodes : Nodes
real-nodes = record
  { Node = ⊤
  ; Child = λ _ → Bool
  ; label = λ _ → real-label }

real-answer : ∀ c d → Answer (real-label c) (real-label d)
real-answer false false = inj₂ (inj₁ refl)
real-answer false true = inj₁ (z≤ (real-label true) , no-nd-zero)
real-answer true false = inj₂ (inj₂ (z≤ (real-label true) , no-nd-zero))
real-answer true true = inj₂ (inj₁ refl)

real-scope : ∀ c d → Scope real-nodes (real-label c) (real-label d)
real-scope c d = tt , c , d , refl , refl

no-real-top : ∀ c → real-label c ≡ tw 1 → ⊥
no-real-top false ()
no-real-top true ()

no-real-cover : Covers real-nodes → ⊥
no-real-cover cover with cover zero (tw 1)
... | tt , c , d , ex , ey = no-real-top d ey

real-table : (t : Table) (c d : Bool) → Maybe ((real-label d ≤ real-label c) Data.Sum.Base.⊎
                                                           (real-label c ≤ real-label d))
real-table minimal c d = proj₁ (MT.rbᶻ (tw 1)) (real-child c) (real-child d)
real-table keel c d = proj₁ (CW.rbᵗ 1) (real-child c) (real-child d)

real-entry : ∀ t → Present (real-table t false true)
real-entry minimal = present (inj₂ (z≤ (real-label true)))
real-entry keel = present (inj₂ (lift zero (↑ zero (real-child true))))

real-entry-back : ∀ t → Present (real-table t true false)
real-entry-back minimal = present (inj₁ (z≤ (real-label true)))
real-entry-back keel = present (inj₁ (lift zero (↑ zero (real-child true))))

completion : ∀ t c d → (real-label c ≡ real-label d) ⊎ Present (real-table t c d)
completion t false false = inj₁ refl
completion t false true = inj₂ (real-entry t)
completion t true false = inj₂ (real-entry-back t)
completion t true true = inj₁ refl

real-evidence : ∀ t → Evidence (Scope real-nodes)
real-evidence t = record
  { E = λ x y → Data.Product.Base.Σ Bool λ c → Data.Product.Base.Σ Bool λ d →
      (real-label c ≡ x) × (real-label d ≡ y) × ((real-label c ≡ real-label d) ⊎ Present (real-table t c d))
  ; answer = λ { _ _ (c , d , refl , refl , _) → real-answer c d }
  ; provide = λ { _ _ (tt , c , d , refl , refl) → c , d , refl , refl , completion t c d } }

real-diagonal-hole : ∀ t → real-table t true true ≡ nothing
real-diagonal-hole minimal = refl
real-diagonal-hole keel = refl

no-real-diagonal-entry : ∀ t → Present (real-table t true true) → ⊥
no-real-diagonal-entry minimal ()
no-real-diagonal-entry keel ()

real-diagonal-answer : Answer (real-label true) (real-label true)
real-diagonal-answer = real-answer true true

no-real-full-table : ∀ t → ((c d : Bool) → Present (real-table t c d)) → ⊥
no-real-full-table t full = no-real-diagonal-entry t (full true true)
```
