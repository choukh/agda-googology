# 累加的读回: 合法闭项

> 判决: 成品候选. 编译定理, 无前提: 累加的塔各项与 `Λᶜ` 的 Ω 树的 ψ₀ 值合法 (`ctwᶜ-leg`, `cEBOᶜ-leg`), 是 `YiLimLegal.twᶜ-leg`, `EBOᶜ-leg` 的对应物 (那里的 `twᶜ` 是旧塔的闭项, 与本路的塔 `twᶜ` 同名不同物).
> 折叠与合法性定理都不改, 直接套 `YiLimLegal.ψ₀-leg` (它对一切带 `Ev`, `Rt` 的层号成立). 不涉及值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumLegal where

open import Data.Nat using (ℕ)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (Leg; Ωt-leg)
open import OCF.Lean.YiLimFold using (ψ₀)
open import OCF.Lean.YiLimLegal using (ψ₀-leg)
open import OCF.Lean.YiCumBlock

ctwᶜ : ℕ → Tr zero
ctwᶜ n = ψ₀ (twᶜ n) (Ev-twᶜ n) (Rtᶜ-tw n) (Ωt (twᶜ n))

ctwᶜ-leg : (n : ℕ) → Leg zero (ctwᶜ n)
ctwᶜ-leg n = ψ₀-leg (twᶜ n) (Ev-twᶜ n) (Rtᶜ-tw n) (Ωt (twᶜ n)) (Ωt-leg (twᶜ n))

cEBOᶜ : Tr zero
cEBOᶜ = ψ₀ Λᶜ Ev-Λᶜ Rt-Λᶜ (Ωt Λᶜ)

cEBOᶜ-leg : Leg zero cEBOᶜ
cEBOᶜ-leg = ψ₀-leg Λᶜ Ev-Λᶜ Rt-Λᶜ (Ωt Λᶜ) (Ωt-leg Λᶜ)
```
