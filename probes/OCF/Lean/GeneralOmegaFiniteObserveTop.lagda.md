# 全有限最高节点的完整typed反馈身份

本篇把新运行器的真实相邻层输出接到已证Seeded原型：旧Ω全部保留，
反馈种子是原floor，迭代没有累加。输出只是NoSum的尾列；两整树的
值比较使用原型的单调性，不将该高层值关系穿过进一步观察器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteObserveTop where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
import OCF.Lean.GeneralOmegaSeededIf as Seed
import OCF.Lean.GeneralOmegaSeededRun as Proof
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Lean.BoundedDiagonalSame using (same-refl; same-add)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)

module At (n : ℕ) where
  module P = Seed.Prototype (F n) (floor n)
  module Q = Proof.Run (F n) (floor n)
  mul-same : ∀ {a b} → Same a b → ∀ i → Same (leftMul a i) (P.leftMul b i)
  mul-same p zero = zz
  mul-same p (suc i) = same-add p (mul-same p i)
  keep-cross : ∀ {a b} → Same a b →
    Same (observe (lower here) (up a)) (P.Typed b)
  keep-cross zz = same-refl (floor n)
  keep-cross (ss p) = ll (mul-same (keep-cross p))
  keep-cross (ll p) = ll (λ i → keep-cross (p i))
  keep-cross (oo p) = oo (λ e → keep-cross (p e))
  callback : HB (F n) → HB (F n)
  callback c = observe (lower here) (up c)
  coordinates : ∀ i → Same (iterate callback (floor n) i) (P.NoSum i)
  coordinates zero = same-refl (floor n)
  coordinates (suc i) = keep-cross (coordinates i)
  outputs : ∀ i → Same (callback (iterate callback (floor n) i)) (P.NoSum (suc i))
  outputs i = keep-cross (coordinates i)
  whole : Same (observe (lower here) (floor (suc n))) (hl (λ i → P.NoSum (suc i)))
  whole = ll outputs

  noSum-mono : ∀ i → P.NoSum i ≤ᵛ P.NoSum (suc i)
  noSum-mono zero = Q.seed-lower (floor n)
  noSum-mono (suc i) = Q.typed-mono (noSum-mono i)
  typed-lower : P.whole ≤ᵛ observe (lower here) (floor (suc n))
  typed-lower = l≤ (λ i → ≤l i (≤-trans (noSum-mono i) (same-value (same-sym (outputs i)))))
  typed-upper : observe (lower here) (floor (suc n)) ≤ᵛ P.whole
  typed-upper = l≤ (λ i → ≤l (suc i) (same-value (outputs i)))
```

这是一条对全部有限n的完整一步值定理。真正目标0在n>0时会继续
处理这些旧Ω；typed-lower/upper不能自动传过该观察。全有限stage
与原记号参照的末段桥仍须另证。
