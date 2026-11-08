# 有限族与原stage 1的真实同界输入

公共界就是原stage 1本身，而非额外制造的上界。下列字段全部实填，
但不包含Γ保序，因此不能单凭它们声称有限输出族已进入最终闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableCaptureInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (stage; stage-legal)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg)
open import OCF.Lean.GeneralOmegaCountableRegularRun using (regular-stage)
open import OCF.Lean.GeneralOmegaCountableCapturePath
  using (first-sum; num-path; sum-large)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

finite-in-stage : ∀ n → num n ⊲ stage 1
finite-in-stage n = hlim 0 (hlim n branch)
  where
  branch : num n ⊲ Σ₀ (λ j → leg (leftMul (hs hz) j)) n
  branch rewrite first-sum n = num-path (sum-large (λ j → j) n)
finite-stage-value : ∀ n → num n ≤ᵛ stage 1
finite-stage-value n = position-value (finite-in-stage n)
finite-regular : ∀ n → Reg (num n)
finite-regular zero = tt
finite-regular (suc n) = finite-regular n
finite-legal : ∀ n → LgB (num n)
finite-legal = num-legal
common-legal : LgB (stage 1)
common-legal = stage-legal 1
right-regular : Reg (stage 1)
right-regular = regular-stage 1
right-in-common : stage 1 ⊲ stage 1
right-in-common = hself
```

finite-in-stage覆盖所有n，不是有限测试。值界只读取已构造的原路径。
原Γ(stage 1)=stage 2的输出覆盖仍需要额外的、可实例化的观察比较。
