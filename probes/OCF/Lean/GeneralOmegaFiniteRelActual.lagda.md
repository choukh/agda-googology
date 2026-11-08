# 全有限真实地板的跨up值桥与阶段增长

只在最终0层把Rel转成Same。原stage(n+1)最高Ω的首个真实反馈坐标
正是floor n，故跨up桥使整个stage n进入stage(n+1)，不只比较常值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteRelActual where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.GeneralOmegaFiniteObserveClosed using (zero-path; stage; tree; stage-lower)
open import OCF.Lean.GeneralOmegaFiniteRelIf
open import OCF.Lean.GeneralOmegaFiniteRelRun
open import OCF.Lean.GeneralOmegaFiniteRelUp
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)

zero-same : ∀ {a b} → Rel zero a b → Same a b
zero-same rz = zz
zero-same (rs p) = ss (zero-same p)
zero-same (rl p) = ll (λ i → zero-same (p i))
zero-same (ro {κ = ()} p)
observe-same : ∀ {n a b} (p : Within n zero) → Rel n a b → Same (observe p a) (observe p b)
observe-same p r = zero-same (observe-related p r)
up-same : ∀ {n a b} (p : Within n zero) → Rel n a b → Same (observe p a) (observe (lower p) (up b))
up-same p r = zero-same (up-observe p r)

stage-up : ∀ n → Same (stage n) (observe (zero-path (suc n)) (up (floor n)))
stage-up n = up-same (zero-path n) (floor-related n)
stage-rise : ∀ n → stage n ≤ᵛ stage (suc n)
stage-rise n = ≤l zero (same-value (stage-up n))

related-value : ∀ {n a b} (p : Within n zero) → Rel n a b → observe p a ≤ᵛ observe p b
related-value p r = same-value (observe-same p r)
related-value-back : ∀ {n a b} (p : Within n zero) → Rel n a b → observe p b ≤ᵛ observe p a
related-value-back p r = same-value (same-sym (observe-same p r))

all-floor-values : ∀ n → observe (zero-path n) (floor n) ≤ᵛ tree
all-floor-values = stage-lower
```

stage-rise直接使用原运行器的首反馈与完整跨up定理。关系域包括原
floor全族，非空且含所有有限旧Ω；尚不等于记号ψ₀(Ω_n)的整族
验收，也没有把任意raw Same提升成Rel。
