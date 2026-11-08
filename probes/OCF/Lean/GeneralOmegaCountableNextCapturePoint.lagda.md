# 非有限高度逐点地板的原观察下界

此辅助树保留原种类结构与Ω分支，只把高度极限处的累计地板拆成
逐点分量。它不替换原floor、observe或Γ，也不要求辅助树合法。
完整原观察对这个辅助输入的输出，由原累计地板输出覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableNextCapturePoint where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure
  using (up-sim; iota-sim; right-add; complete)
open import OCF.Lean.GeneralOmegaCountableRegularCompareRun using (compare)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

pointFloor : ∀ B → HB (F B)
pointFloor hz = hs hz
pointFloor (hs B) = hΩ (inj₂ tt) (λ e → up e)
pointFloor (hl f) = hl (λ n → ι n (pointFloor (f n)))
pointFloor (hΩ () g)

point-floor : ∀ B → Sim B (pointFloor B) (floor B)
point-floor hz = ss sz
point-floor (hs B) = so up-sim
point-floor (hl f) = sl partial
  where
  partial : ∀ n → Sim (hl f) (ι n (pointFloor (f n))) (C.ΣT S⊥ (hs hz) f n)
  partial zero = iota-sim (point-floor (f zero))
  partial (suc n) = right-add (iota-sim (point-floor (f (suc n)))) (C.ΣT S⊥ (hs hz) f n)
point-floor (hΩ () g)

observed-point : ∀ B lB pt →
  leg (observe B lB hz pt (pointFloor B)) ≤ᵛ leg (observe B lB hz pt (floor B))
observed-point B lB pt = complete (compare B lB hz pt (point-floor B))
actual-Γ : ∀ c →
  leg (observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (pointFloor (leg c))) ≤ᵛ Γ c
actual-Γ c = observed-point (leg c) (Lg-leg c) (z⊲ᴮ (leg c))

-- 原ω高度的完整观察，不只选择某个有限分量。
omega-instance :
  leg (observe omega omega-legal hz (z⊲ᴮ omega) (pointFloor omega)) ≤ᵛ
  leg (observe omega omega-legal hz (z⊲ᴮ omega) (floor omega))
omega-instance = observed-point omega omega-legal (z⊲ᴮ omega)
```

这排除了把“原输入地板累计”本身视作未处理差异：完整观察已有有向
覆盖。尚未比较两个不同运行器；内部ψ反馈的零叶和初始种子仍须按
各自真实低层地板耦合，不能把本定理误读为任意记号输入已验收。
