# 指定分量的完整输出捕获

将原单分量source的完整观察经实际ι搬入同一合法并层，再用已证
右分量累计吸收。右侧保留hlim n目标路径，未擅自换成Γ的规范路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareCapture where
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveLimit using (limit-observe)
open import OCF.Lean.GeneralOmegaCountableRelRun using (floor-related)
open import OCF.Lean.GeneralOmegaCountableRelActual using (zero-same)
open import OCF.Lean.GeneralOmegaCountableRegularCompareActual using (component-completed)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)

component-capture : ∀ f lB n (pt : hz ⊲ f n) →
  leg (observe (f n) (proj₂ lB n) hz pt (floor (f n))) ≤ᵛ
  leg (observe (hl f) lB hz (hlim n pt) (floor (hl f)))
component-capture f lB n pt = ≤-trans
  (same-value (leg-same (zero-same (limit-observe f lB n hz pt (floor-related (f n))))))
  (component-completed f lB (hlim n pt) n)
```

本定理的前提对任意合法并层及每个原分量都可满足，pt可取z⊲ᴮ。
它比较的是原函数完整输出及原leg，不是改造过的轨道或只取首项。
Γ还先完成输入高度；该输入变化以及规范目标路径运输仍分别列账。
