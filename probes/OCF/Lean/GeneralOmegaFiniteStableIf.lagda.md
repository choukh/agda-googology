# 完成预算之前的真实全阶段计算接口

stage-rise不足以提供leg稳定。本篇先要求精确识别原下一阶段的全部
可数观察项：它们是原floor种子、无累加typed轨道的低层观察。该式
不把高层值关系穿过observe，也不把完成稳定写成未实例化前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteStableIf where
open import Data.Nat using (ℕ; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf using (F; floor)
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.GeneralOmegaFiniteObserveClosed using (stage; zero-path)
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)
open import OCF.Lean.FrozenWorldLift using (Same)

read-orbit : ℕ → ℕ → Cd
read-orbit n i = observe (zero-path n) (Prototype.NoSum (F n) (floor n) i)
record StageEquation : Set where
  field
    whole : ∀ n → Same (stage (suc n)) (hl (read-orbit n))
```

接口已逐字保留原stage、observe与Seeded.NoSum。其后仍需证明这些
实际read-orbit的完成/部分和预算，不能把本式称为leg保值。
