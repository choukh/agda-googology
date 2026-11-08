# 用遗传关系展开原全部后继阶段

先在原低层HB中把完整反馈链关联到Seeded.NoSum，随后才调用跨up
观察模拟。整个过程中没有将高层Same或高层值序喂给任意观察器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteStableRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.GeneralOmegaFiniteObserveClosed using (stage; zero-path)
open import OCF.Lean.GeneralOmegaFiniteRelIf
open import OCF.Lean.GeneralOmegaFiniteRelRun using (floor-related; add-rel)
open import OCF.Lean.GeneralOmegaFiniteRelUp using (up-observe)
open import OCF.Lean.GeneralOmegaFiniteRelActual using (zero-same)
open import OCF.Lean.GeneralOmegaFiniteStableIf
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-sym; same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

module At (n : ℕ) where
  module P = Prototype (F n) (floor n)
  callback : HB (F n) → HB (F n)
  callback c = observe (lower here) (up c)
  left-cross : ∀ {a b} → Rel n a b → ∀ i → Rel n (P.leftMul a i) (leftMul b i)
  left-cross p zero = rz
  left-cross p (suc i) = add-rel p (left-cross p i)
  typed-back : ∀ {a b} → Rel n a b → Rel n (P.Typed a) (callback b)
  typed-back rz = floor-related n
  typed-back (rs p) = rl (left-cross (typed-back p))
  typed-back (rl p) = rl (λ i → typed-back (p i))
  typed-back (ro p) = ro (λ cd → typed-back (p cd))
  coordinates-back : ∀ i → Rel n (P.NoSum i) (iterate callback (floor n) i)
  coordinates-back zero = floor-related n
  coordinates-back (suc i) = typed-back (coordinates-back i)
  outputs : ∀ i → Same
    (observe (zero-path (suc n)) (up (iterate callback (floor n) i))) (read-orbit n i)
  outputs i = same-sym (zero-same (up-observe (zero-path n) (coordinates-back i)))

whole : ∀ n → Same (stage (suc n)) (hl (read-orbit n))
whole n = ll (At.outputs n)
whole-lower : ∀ n → hl (read-orbit n) ≤ᵛ stage (suc n)
whole-lower n = same-value (same-sym (whole n))
whole-upper : ∀ n → stage (suc n) ≤ᵛ hl (read-orbit n)
whole-upper n = same-value (whole n)
instance-equation : StageEquation
instance-equation = record { whole = whole }
```

本式已经实填所有有限n的真实floor/observer反馈，而非未实例化
Series条件。完成桥剩下的具体问题是：原read-orbit的完成项与部分
和，能否在后续实际read-orbit或更高stage中获得统一预算；这里未证。
