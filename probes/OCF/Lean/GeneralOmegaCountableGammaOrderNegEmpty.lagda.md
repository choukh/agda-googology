# 同界合法零值输入不能保证原Γ值单调

本篇保持原Γ、完成和累计地板不变。两个输入都是合法零值树，
共同界取原空极限；否定的只是冻结接口中的值单调字段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableGammaOrderNegEmpty where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.GeneralOmegaCountableGammaOrderIf
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (rawΓ; Γ)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.CountableCompletionUpperOmega using (num; ω; leg-ω≤ω; add-mono)
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-value; same-sym)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

ones : ∀ n → leftMul (hs hz) n ≡ num n
ones zero = refl
ones (suc n) rewrite ones n = plus-one n
  where
  plus-one : ∀ n → hs hz ⊞ num n ≡ hs (num n)
  plus-one zero = refl
  plus-one (suc n) rewrite plus-one n = refl

zero-shape : Same (rawΓ hz) ω
zero-shape = ll each
  where
  each : ∀ n → Same (leftMul (hs hz) n) (num n)
  each n rewrite ones n = same-refl _
zero-upper : Γ hz ≤ᵛ ω
zero-upper = ≤-trans (same-value (leg-same zero-shape)) leg-ω≤ω

strict-empty-raw : hs ω ≤ᵛ rawΓ empty-limit
strict-empty-raw = ≤l 1 (≤l 2
  (add-mono (same-value (same-sym zero-shape)) (≤l 1 (≤-refl _))))
strict-empty : hs ω ≤ᵛ Γ empty-limit
strict-empty = ≤-trans strict-empty-raw (inflation (rawΓ empty-limit))
not-back : Γ empty-limit ≤ᵛ Γ hz → ⊥
not-back p = ¬s≤ᵛ ω (≤-trans strict-empty (≤-trans p zero-upper))
no-bounded-value-monotone : BoundedValueMonotone → ⊥
no-bounded-value-monotone m = not-back
  (BoundedValueMonotone.monotone m empty-legal empty-legal tt
    empty-in-common zero-in-common empty≤zero)
```

zero-upper控制原Γ0；strict-empty-raw选择原累计地板第1分量的完整
观察输出，再选其第2项。这里不是替换成玩具模型。该结果不否定
指定后继的严格增长、总定义或可数高度路线，也不给最终迭代树上界。
