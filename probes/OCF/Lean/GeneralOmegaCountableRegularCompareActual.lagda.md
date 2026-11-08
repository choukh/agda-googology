# 原累计地板的全部右分量完成捕获

此前只有左前缀包含。这里以原floor的遗传有向自证，先把指定右
分量送入其真实部分和，再送入整个原地板。观察路径在两侧逐字
相同，完成运输来自结构Sim而不是一般值单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareActual where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure
open import OCF.Lean.GeneralOmegaCountableRegularCompareRun
open import OCF.Lean.Fold1If using (_≤ᵛ_)

component-partial : ∀ f n → Sim (hl f) (ι n (floor (f n))) (C.ΣT S⊥ (hs hz) f n)
component-partial f zero = iota-sim (floor-self (f zero))
component-partial f (suc n) = right-add (iota-sim (floor-self (f (suc n)))) (C.ΣT S⊥ (hs hz) f n)
component-floor : ∀ f n → Sim (hl f) (ι n (floor (f n))) (floor (hl f))
component-floor f n = sli n (component-partial f n)
component-output : ∀ f lB pt n → Sim hz
  (observe (hl f) lB hz pt (ι n (floor (f n))))
  (observe (hl f) lB hz pt (floor (hl f)))
component-output f lB pt n = compare (hl f) lB hz pt (component-floor f n)
component-completed : ∀ f lB pt n →
  leg (observe (hl f) lB hz pt (ι n (floor (f n)))) ≤ᵛ
  leg (observe (hl f) lB hz pt (floor (hl f)))
component-completed f lB pt n = complete (component-output f lB pt n)
```

定理包含全部原分量、全部合法共同高度和原目标路径，无外加回调
同余前提。它尚未把单分量观察的hlim n目标路径与完整Γ的规范
hlim 0路径统一；该独立运输义务不能由组件值相等省去。
