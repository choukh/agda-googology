# 相邻阶段吸收重复时，外层完成保值

各阶段已完成保值还不够，外层leg会把阶段输出再累加。下面另要求
下一阶段覆盖当前阶段的ω重复，明确控制这一次外层累加。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCompletionSeries where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l; l≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Lean.GeneralOmegaCompletionRun using (parts-mono)

record Stages (f : ℕ → Cd) : Set where
  field
    stable : ∀ n → leg (f n) ≤ᵛ f n
    growth : ∀ n → Ops.repeat S⊥ (f n) ≤ᵛ f (suc n)

module Result (f : ℕ → Cd) (stages : Stages f) where
  open Stages stages
  stage-step : ∀ n → f n ≤ᵛ f (suc n)
  stage-step n = ≤-trans (≤l 0 (≤-refl _)) (growth n)
  completed-parts : ∀ n → Σ₀ (λ j → leg (f j)) n ≤ᵛ
    Ops.partial S⊥ (λ _ → f n) n
  completed-parts zero = stable zero
  completed-parts (suc n) = add-mono
    (≤-trans (completed-parts n) (parts-mono (λ _ → stage-step n) n)) (stable (suc n))

  upper : leg (hl f) ≤ᵛ hl f
  upper = l≤ (λ n → ≤l (suc n)
    (≤-trans (completed-parts n) (≤-trans (≤l n (≤-refl _)) (growth n))))
```

此处阶段是原树输出族，关系不是下标判等或三歧。每项都必须给实际
实例，不能从各层的源名字或已有下界推断stable/growth。最终Λ源族
是否满足它，仍应由真实原运行器与原ΣF证明。
