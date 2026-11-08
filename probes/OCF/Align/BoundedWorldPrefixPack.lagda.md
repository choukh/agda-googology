# 原中 Ω 有限输出和的状态与输入联合打包

共同中槽取原 ce n，不取外部常量。源输入是全部真实分支的padding；
原Col.oO与Σ₀之间显式归纳连接，不把数组别名的展开当证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldPrefixPack where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; up-value; floor-value)
open import OCF.Align.BoundedWorldValueTwoSlot
import OCF.Align.BoundedWorldPrefixIf as If
import OCF.Align.BoundedWorldPrefixRun as Run
import OCF.Lean.TwoSlotValueRun as Joint
import OCF.Lean.TwoSlotValuePadding as Padding

module Pack (u : Cd) (b : HB U) (p : HB V) (bb : Value hz b b) (pp : Value (hs hz) p p) where
  module M = If.Middle u b p
  module Self = Run.Compare (≤-refl u) bb pp

  current : ∀ n → M.cw n ≡ M.ce n
  current zero = refl
  current (suc n) = refl

  initial-bound : ∀ n → Value hz b (M.ce n)
  initial-bound zero = bb
  initial-bound (suc n) = prefix-rel (initial-bound n) _

  next-mono : ∀ {j n} → Value hz (M.ce j) (M.ce n) → Value hz
    (mid (M.cw j) (p ⊞ up (M.ce j))) (mid (M.cw n) (p ⊞ up (M.ce n)))
  next-mono {j} {n} r rewrite current j | current n = Joint.middle (add-rel pp (up-value hz r)) r

  coordinate-bound : ∀ {j n} → j ≤ n → Value hz (M.ce j) (M.ce n)
  coordinate-bound {n = n} z≤n = initial-bound n
  coordinate-bound (s≤s q) = add-rel (coordinate-bound q) (next-mono (coordinate-bound q))

  slot-bound : ∀ n j → j ≤ n → Value hz (M.cw j) (M.ce n)
  slot-bound n j q rewrite current j = coordinate-bound q

  branch : ℕ → HB V
  branch j = p ⊞ up (M.ce j)
  branch-self : ∀ j → Value (hs hz) (branch j) (branch j)
  branch-self j = add-rel pp (up-value hz (Self.coordinates j))
  sourcePad : ℕ → HB V
  sourcePad n = Padding.pad branch n
  sourcePad-self : ∀ n → Value (hs hz) (sourcePad n) (sourcePad n)
  sourcePad-self = Padding.pad-self branch branch-self

  col-sum : ∀ n → Σ₀ (λ j → low u (M.cw j) (branch j)) n ≡ M.oO n
  col-sum zero = refl
  col-sum (suc n) = cong₂ _⊞_ (col-sum n) refl

  packed : ∀ n → M.oO n ≤ᵛ low u (M.ce n) (sourcePad n)
  packed n = subst (λ x → x ≤ᵛ low u (M.ce n) (sourcePad n)) (col-sum n)
    (Padding.sum≤pad branch branch-self M.cw (λ _ → u) n (M.ce n) u
      (Self.coordinates n) (slot-bound n) (λ j q → ≤-refl u))
```

下列实例使用原第三地板的真实非零前缀及实际feedback底槽。

```agda
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Lean.TwoSlotValueClosure using (coordinate-self)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedWorldPrefixSeed as Seed
import OCF.Align.BoundedNativeValueFirst as First

module Actual = Pack First.feedback (floor zero) (Whole.Model.ce 1)
  (floor-value zero) (coordinate-self 1)

actual-prefix : Whole.Model.ce 1 ≡ Seed.prefix
actual-prefix = refl

actual-packed : ∀ n →
  If.Middle.oO First.feedback (floor zero) Seed.prefix n ≤ᵛ
  low First.feedback (If.Middle.ce First.feedback (floor zero) Seed.prefix n) (Actual.sourcePad n)
actual-packed = Actual.packed
```

这是真实全部有限输出和的联合上界，右端两部分都随n增长。它为跨
Uniform覆盖提供具体义务：同步覆盖ce n与sourcePad n；尚未证明该同步
覆盖，也没有声称这里的右端已低于C。
