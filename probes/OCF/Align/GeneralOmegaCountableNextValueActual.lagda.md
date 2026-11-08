# 原完整γ₁参数的下一次Γ调用

验收专用。不是选取γ₁的有限样本，而是以整个原γ₁为参数，证明
其完成后进入Γ的调用与原stage 2结构对应。这里Γ仍是原树侧函数，
没有把旧记号的γ₂定义换名成Γ输出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableNextValueActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; rawΓ; stage; tree; stage-lower)
open import OCF.Lean.GeneralOmegaCountableSuccessorRun using (gamma-whole)
open import OCF.Lean.GeneralOmegaCountableShapeRun using (Γ-same)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (same-trans; leg-same)
open import OCF.Lean.FrozenWorldLift using (Same; same-sym; same-value)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
import OCF.Lean.GeneralOmegaCountableNextCapturePointActual as Point
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.NoCumsum as N
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (whole-shape)

reference-raw-shape : Same (B.forget (N.γ 1)) (rawΓ (hs hz))
reference-raw-shape = same-trans whole-shape (same-sym (gamma-whole hz))
reference-stage-shape : Same (leg (B.forget (N.γ 1))) (stage 1)
reference-stage-shape = leg-same reference-raw-shape
next-call-shape : Same (Γ (leg (B.forget (N.γ 1)))) (stage 2)
next-call-shape = Γ-same reference-stage-shape

-- 原Γ会再完成自己的输入，因此下面保留真实双leg，不擅自幂等化。
height : Cd
height = leg (leg (B.forget (N.γ 1)))
auxiliary : Cd
auxiliary = leg (point-observe height (Lg-leg (leg (B.forget (N.γ 1))))
  hz (z⊲ᴮ height) (pointFloor height))
auxiliary≤stage2 : auxiliary ≤ᵛ stage 2
auxiliary≤stage2 = ≤-trans (Point.actual-Γ (leg (B.forget (N.γ 1))))
  (same-value next-call-shape)
auxiliary≤tree : auxiliary ≤ᵛ tree
auxiliary≤tree = ≤-trans auxiliary≤stage2 (stage-lower 2)
```

剩余的原记号义务是forget(γ₂)≤auxiliary，尚未证明。上式已将该
具体辅助输出无条件送入原闭项；它不是以未证前提冒充γ₂下界。
特别地，height保留双重完成，其与原toLevel(γ₁)的异层坐标模拟仍需证明。
