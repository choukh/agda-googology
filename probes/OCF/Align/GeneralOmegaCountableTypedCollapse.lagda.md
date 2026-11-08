# 内部目标的same与above完整坍缩节点

验收专用。源kind秩先沿原ClassLink的字面等式规范化；同层反馈
保留源秩与目标两份诱导合法证，以实际层同构作Read运输。高层
反馈沿原pi的内部目标运行，两个分支都保完整无累加列及原种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedCollapse where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; iterate; module C)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe; point-node)
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (H)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass using (cast)
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read; self)
open import OCF.Align.GeneralOmegaCountableTypedProofVia using (transport-via)
open import OCF.Align.GeneralOmegaCountableTypedDispatch
open import OCF.Align.GeneralOmegaCountableTypedValueObserveRecursor using (Result)
import OCF.Align.GeneralOmegaCountableTypedValueObserveFeedback as Feedback
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

module SameRank (B : Cd) (lB : LgB B) (i : Cd) (pi ht : hs i ⊲ B)
  {ℓ : L.Ordᴵ} {A : Set} (σ : L.Simᴵ ℓ (height B lB))
  (q : height i (lgB⊲ pi tt lB) L.<ᴵ ℓ)
  (f : L.U _ (L.<→◃ q) → L.Ordᶜ ℓ)
  (g : A → HB (F B)) (encode : HB (F i) → A)
  (sub : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) x)) (g (encode e)))
  (ih : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Result B lB σ (f (L.into (L.<→◃ q) x)) (g (encode e))) where
  li = lgB⊲ pi tt lB
  lt = lgB⊲ ht tt lB
  same-index = height-shape (same-refl i) li lt
  old : ℕ → L.Ordᶜ (height i li)
  old = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω (height i li))
  new : ℕ → HB (F i)
  new = iterate (λ e → point-observe B lB i (⊲ᴮ-tr (hsuc hself) ht) (g (encode e))) (pointFloor i)
  coordinates : ∀ n → Read i li (canonical i li) (old n) (new n)
  coordinates zero = floor-read i li
  coordinates (suc n) = rc
    (L.≅-tr⁻ same-index (L.ψ-≅ {p = q} {σ = λ r → r}
      {p′ = index-bound lB ht} {σ′ = σ} same-index (self (sub (old n) (new n) (coordinates n)))))
    (transport-via i li lt same-index (Result.internal (ih (old n) (new n) (coordinates n)) i ht))
  outputs : ∀ n → Read i lt (canonical i lt)
    (L.ψ (index-bound lB ht) σ (f (L.into (L.<→◃ q) (old n))))
    (point-observe B lB i (⊲ᴮ-tr (hsuc hself) ht) (g (encode (new n))))
  outputs n = Result.internal (ih (old n) (new n) (coordinates n)) i ht

same-at-rank : ∀ B lB (i : Cd) (pi ht : hs i ⊲ B) j
  (eq : j ≡ height i (lgB⊲ pi tt lB)) {ℓ : L.Ordᴵ} {A : Set}
  (σ : L.Simᴵ ℓ (height B lB)) (q : j L.<ᴵ ℓ)
  (f : L.U j (L.<→◃ q) → L.Ordᶜ ℓ) (g : A → HB (F B)) (encode : HB (F i) → A)
  (sub : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  (∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Result B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  Read i (lgB⊲ ht tt lB) (canonical i (lgB⊲ ht tt lB))
    (L.ψ (index-bound lB ht) σ (L.limᵢ q f))
    (point-node (⊲ᴮ-tr (hsuc hself) ht) (C.same encode)
      (λ t p e → point-observe B lB t p (g e)))
same-at-rank B lB i pi ht ._ refl σ q f g encode sub ih
  with L.<ᴵ-dec (σ q) (index-bound lB ht) |
    equal-consistent (height-shape (same-refl i) (lgB⊲ pi tt lB) (lgB⊲ ht tt lB))
      (L.<ᴵ-dec (σ q) (index-bound lB ht))
... | inj₂ (inj₂ eqv) | equal .eqv = rl Chain.outputs
  where module Chain = SameRank B lB i pi ht σ q f g encode sub ih

above-at-rank : ∀ B lB t (ht : hs t ⊲ B) (i : Cd) (pi : hs i ⊲ B)
  (tr : t ⊲ i) → hs (H t) ≤ᵛ H i → ∀ j
  (eq : j ≡ height i (lgB⊲ pi tt lB)) {ℓ : L.Ordᴵ} {A : Set}
  (σ : L.Simᴵ ℓ (height B lB)) (q : j L.<ᴵ ℓ)
  (f : L.U j (L.<→◃ q) → L.Ordᶜ ℓ) (g : A → HB (F B)) (encode : HB (F i) → A)
  (sub : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  (∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Result B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
    (L.ψ (index-bound lB ht) σ (L.limᵢ q f))
    (point-node (⊲ᴮ-tr (hsuc hself) ht) (C.above i pi tr encode)
      (λ r p e → point-observe B lB r p (g e)))
above-at-rank B lB t ht i pi tr strict ._ refl σ q f g encode sub ih
  with L.<ᴵ-dec (σ q) (index-bound lB ht) |
    upper-consistent (above-order lB ht pi strict) (L.<ᴵ-dec (σ q) (index-bound lB ht))
... | inj₂ (inj₁ v) | upper .v = rl (λ n →
  Result.internal (ih (Chain.old n) (Chain.new n) (Chain.coordinates n)) t ht)
  where
  module Chain = Feedback.Chain B lB i pi σ q f (λ e → g (encode e)) sub
    (λ x e r → Result.internal (ih x e r) i pi)
```

两个结果都仍以原source子树的Result为前提，供总递归实际填入。
它们没有改运行器、忽略异合法证运输或假定整个ψ观察定理已经成立。
