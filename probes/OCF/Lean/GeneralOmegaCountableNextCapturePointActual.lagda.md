# 逐点辅助解释的实际完整输出界

全部B的原累计floor及辅助pointFloor均有实际Sim前提；目标零完成
只使用已证结构complete，不把普通值序直接运输过leg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableNextCapturePointActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor; point-floor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointRun using (simulate)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf using (Sim)
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure using (floor-self; complete)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

completed : ∀ B lB pt {a b} → Sim B a b →
  leg (point-observe B lB hz pt a) ≤ᵛ leg (observe B lB hz pt b)
completed B lB pt r = complete (simulate B lB hz pt r)
whole-point : ∀ B lB pt →
  leg (point-observe B lB hz pt (pointFloor B)) ≤ᵛ leg (observe B lB hz pt (floor B))
whole-point B lB pt = completed B lB pt (point-floor B)
whole-floor : ∀ B lB pt →
  leg (point-observe B lB hz pt (floor B)) ≤ᵛ leg (observe B lB hz pt (floor B))
whole-floor B lB pt = completed B lB pt (floor-self B)
actual-Γ : ∀ c →
  leg (point-observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (pointFloor (leg c))) ≤ᵛ Γ c
actual-Γ c = whole-point (leg c) (Lg-leg c) (z⊲ᴮ (leg c))
omega-instance :
  leg (point-observe omega omega-legal hz (z⊲ᴮ omega) (pointFloor omega)) ≤ᵛ
  leg (observe omega omega-legal hz (z⊲ᴮ omega) (floor omega))
omega-instance = whole-point omega omega-legal (z⊲ᴮ omega)
```

point-observe的所有低层零叶和反馈种子差异现在都由全轨道模拟处理，
并非仅输入根地板的比较。未建立旧typed记号与辅助解释器的异层Read；
尤其toLevel t到leg(forget t)的高度变化仍未模拟，故不宣称完整γ₂下界。
辅助算法受参照启发，只作研究解释，没有修改原闭项或提供替代FGH。
