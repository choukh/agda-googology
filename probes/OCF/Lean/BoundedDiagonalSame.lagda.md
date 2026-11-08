# 原直接回灌的异坐标结构模拟

以下直接比较已有chain与diagonal，不另写运行器。普通Same只比较相同
坐标的分支；这里的前提明确要求回调接受不同但Same的坐标，再逐项
证明两条真实反馈链、输出及部分和Same。没有从Same推出函数相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedDiagonalSame where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)

same-refl : ∀ {S} (a : HB S) → Same a a
same-refl hz = zz
same-refl (hs a) = ss (same-refl a)
same-refl (hl f) = ll (λ n → same-refl (f n))
same-refl (hΩ κ g) = oo (λ c → same-refl (g c))

same-add : ∀ {S} {a b c d : HB S} → Same a b → Same c d → Same (a ⊞ c) (b ⊞ d)
same-add p zz = p
same-add p (ss q) = ss (same-add p q)
same-add p (ll q) = ll (λ n → same-add p (q n))
same-add p (oo q) = oo (λ c → same-add p (q c))

module Compare {S T : KS}
  (f f′ : HB S → HB S) (g g′ : HB S → HB T)
  (sf : ∀ {a b} → Same a b → Same (f a) (f′ b))
  (sg : ∀ {a b} → Same a b → Same (g a) (g′ b)) where

  coordinates : ∀ n → Same (chain f n) (chain f′ n)
  coordinates zero = ss zz
  coordinates (suc n) = same-add (coordinates n) (sf (coordinates n))

  outputs : ∀ n → Same (g (chain f n)) (g′ (chain f′ n))
  outputs n = sg (coordinates n)

  partials : ∀ n → Same
    (Ops.partial T (λ k → g (chain f k)) n)
    (Ops.partial T (λ k → g′ (chain f′ k)) n)
  partials zero = outputs zero
  partials (suc n) = same-add (partials n) (outputs (suc n))

  result : Same (diagonal f g) (diagonal f′ g′)
  result = ll partials

up-same : ∀ {S} {a b : HB S} → Same a b → Same (up a) (up b)
up-same zz = zz
up-same (ss p) = ss (up-same p)
up-same (ll p) = ll (λ n → up-same (p n))
up-same (oo p) = oo (λ c → up-same (p c))

module Example (S : KS) = Compare (λ (a : HB S) → a) (λ a → a)
  up up (λ p → p) up-same
```

Example给非恒定坐标/输出回调的实际实例，说明前提可满足；这不是新的
序数强度定理。后续原fold桥仍须给实际floor/θ分支递归的异坐标证书。
本篇没有宣称任意g自动保持Same，也没有把缺少该证书写成否定定理。
