# 规范零路径下的完整分量捕获

同一合法source的零目标路径相容由遗传Rel提供。本篇只以原floor
自证消费它，完成运输经Same；不宣称任意目标路径或source高度相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareCanonical where
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableObserveZeroPath using (zero-path-observe)
open import OCF.Lean.GeneralOmegaCountableRelRun using (floor-related)
open import OCF.Lean.GeneralOmegaCountableRelActual using (zero-same)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCapture using (component-capture)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)

collapse : (B : Cd) → LgB B → Cd
collapse B lB = leg (observe B lB hz (z⊲ᴮ B) (floor B))
canonical-component : ∀ f (lB : LgB (hl f)) n →
  collapse (f n) (proj₂ lB n) ≤ᵛ collapse (hl f) lB
canonical-component f lB n = ≤-trans
  (component-capture f lB n (z⊲ᴮ (f n)))
  (same-value (leg-same (zero-same (zero-path-observe (hl f) lB
    (hlim n (z⊲ᴮ (f n))) (z⊲ᴮ (hl f)) (floor-related (hl f))))))

-- 直接原Γ的实际分量：完成输入的分量是累计完成高度，而非原f n。
actual-Γ-component : ∀ f n →
  collapse (Σ₀ (λ k → leg (f k)) n) (proj₂ (Lg-leg (hl f)) n) ≤ᵛ Γ (hl f)
actual-Γ-component f n = canonical-component
  (λ n → Σ₀ (λ k → leg (f k)) n) (Lg-leg (hl f)) n
```

actual-Γ-component实填原Γ及其全部实际完成分量。它不把原f n
换成累计高度，尚需独立的输入高度加法右组件吸收才能从Γ(f n)
推出Γ(hl f)的界；没有把该余项隐藏为值单调假设。
