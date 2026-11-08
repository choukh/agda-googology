# 原观察器与Γ全迭代的正则实例

Built由原运行器实际构造子方程逐项建立。目标0不可能保留Ω种类；
同层与高层节点的全部真实反馈输出都递归原source分支，不另造模型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularRun where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; stage)
open import OCF.Lean.GeneralOmegaCountableRegularIf
open import OCF.Lean.GeneralOmegaCountableRegularClosure

node-built : ∀ {B A} (pt : hz ⊲ B) (v : C.Dc F B hz A)
  (rec : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ e → Built (rec hz pt e)) → Built (node pt v rec)
node-built pt (C.keep () fr) rec p
node-built pt (C.same to) rec p = limit (λ n → p (to (iterate (λ e → rec hz pt (to e)) (floor hz) n)))
node-built pt (C.above i pi ti to) rec p = limit (λ n → p
  (to (iterate (λ e → rec i (⊲ᴮ-tr (hsuc hself) pi) (to e)) (floor i) n)))
built-observe : ∀ B lB pt a → Built (observe B lB hz pt a)
built-observe B lB pt hz = one
built-observe B lB pt (hs a) = repeat (built-observe B lB pt a)
built-observe B lB pt (hl f) = limit (λ n → built-observe B lB pt (f n))
built-observe B lB pt (hΩ κ f) = node-built pt (classify B lB hz pt κ)
  (λ r pr e → observe B lB r pr (f e)) (λ e → built-observe B lB pt (f e))
regular-Γ : ∀ c → Reg (Γ c)
regular-Γ c = complete-built (built-observe (leg c) (Lg-leg c) (z⊲ᴮ (leg c)) (floor (leg c)))
regular-stage : ∀ n → Reg (stage n)
regular-stage zero = tt
regular-stage (suc n) = regular-Γ (stage n)
regular-height : ∀ n → Reg (leg (stage n))
regular-height n = reg-leg (regular-stage n)
instance-regular : RegularConstruction
instance-regular = record
  { built-observe = built-observe
  ; complete-built = complete-built
  ; regular-Γ = regular-Γ
  ; regular-stage = regular-stage
  ; regular-height = regular-height }
```

这是冻结RegularConstruction的完整实际实例。Reg包含每个内部
ℕ极限的严格值步进，因而实际Γ输出及下轮所用完成高度均不含
旧空极限反例。此结论不声称Reg输入之间的Γ值单调成立；该额外
字段仍须独立证明或否定，不在本实例中假定。
