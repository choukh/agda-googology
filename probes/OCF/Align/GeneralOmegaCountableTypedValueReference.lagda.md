# 原Γ全部完成高度的实际typed参照下界

验收专用。参照读取原合法高度自身的height，不把它认作任意另一棵
未完成树的toLevel。整个point-observe已由完整观察实现校准，再由
已证两运行器模拟送进原Γ；不是把规格ψ̂单调当成运行器正确性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueReference where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
import OCF.Lean.GeneralOmegaCountableNextCapturePointActual as Point
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.FrozenWorldLift using (Same; same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedValueObserveActual using (floor-observation)
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (forget-read)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z

reference-shape : ∀ B lB pt →
  Same (Z.forget (L.ψ⁰ (L.Ω (height B lB)))) (point-observe B lB hz pt (pointFloor B))
reference-shape B lB pt = forget-read (floor-observation B lB pt)
reference≤Γ : ∀ c → Z.forget (L.ψ⁰ (L.Ω (height (leg c) (Lg-leg c)))) ≤ᵛ Γ c
reference≤Γ c = ≤-trans (same-value (reference-shape (leg c) (Lg-leg c) (z⊲ᴮ (leg c))))
  (≤-trans (inflation _) (Point.actual-Γ c))

omega-reference-shape :
  Same (Z.forget (L.ψ⁰ (L.Ω (height omega omega-legal))))
    (point-observe omega omega-legal hz (z⊲ᴮ omega) (pointFloor omega))
omega-reference-shape = reference-shape omega omega-legal (z⊲ᴮ omega)
```

reference≤Γ覆盖任意原c，包括所有非有限完成高度。它没有消除旧
γ₁的toLevel与实际双完成高度的差别，因此不据此声称原γ₂下界，
也没有把NoCumsum全γ链等同于EBO全部Ω塔。
