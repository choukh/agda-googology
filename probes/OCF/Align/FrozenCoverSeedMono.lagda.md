# 修复初始生成元的显式前缀对种子值单调

这是固定可数树类型上的值函数定理，不决定下标位置或更新槽。
不从值关系反推第一位置；使用显式纯轨道逐步比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenCoverSeedMono where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_; l≤; ≤l; z≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf using (frozen; changing)
import OCF.Align.FrozenOutputIf as If
open import OCF.Align.FrozenCoverIf using (D)
import OCF.Align.FrozenCoverInitial as I
open import OCF.Align.FrozenAbsorbNegUpper using (P; mono)

module SeedMono (A : Cd) where
  open If.Model A
  C : Cd → Cd
  C b = run frozen hz (up b ⊞ D (top (hs hz)))

  module Compare {b d : Cd} (bd : b ≤ᵛ d) where
    module L = I.Initial.At A b
    module R = I.Initial.At A d
    coordinates : ∀ n → L.R.ce n ≤ᵛ R.R.ce n
    outputs : ∀ n → L.R.oo n ≤ᵛ R.R.oo n
    coordinates zero = z≤
    coordinates (suc n) = add-mono (coordinates n) (outputs n)
    outputs n = mono (≤-refl A) (add-mono (add-mono bd (coordinates n)) (coordinates n))
    sums : ∀ n → L.R.oO n ≤ᵛ R.R.oO n
    sums zero = outputs zero
    sums (suc n) = add-mono (sums n) (outputs (suc n))
    result : C b ≤ᵛ C d
    result = ≤-trans (same-value L.actual-normal)
      (≤-trans (l≤ (λ n → ≤l n (sums n))) (same-value (same-sym R.actual-normal)))

  mono-C : ∀ {b d} → b ≤ᵛ d → C b ≤ᵛ C d
  mono-C = Compare.result

  -- 原双Ω反馈和修复双Ω反馈的规范一步映射。
  old-step new-step : Cd → Cd
  old-step e = P (run changing e (top (hs hz))) e
  new-step e = P (C e) e
  step-cover : ∀ {e f} → e ≤ᵛ f → old-step e ≤ᵛ new-step f
  step-cover {e} ef = mono
    (≤-trans (I.Initial.initial-cover A e) (mono-C ef)) ef
```

`step-cover` 已覆盖动态种子与显式前缀种子的规范一步映射。
它尚未在本篇连接到 D pair 的完整实际回灌，也不能消除 D 的合法性反例。
