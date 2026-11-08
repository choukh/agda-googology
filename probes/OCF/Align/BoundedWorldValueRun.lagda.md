# 原 Col 的全世界模拟

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueRun where
open import Data.Nat using (zero; suc)
open import OCF.Align.BoundedWorldValueIf

module Run {A B S T WR XR TR wa wb a b ua ub fx gx ft gt}
  (sim : Simulation {A} {B} {S} {T} WR XR TR wa wb a b ua ub fx gx ft gt) where
  open Simulation sim
  coordinates : ∀ n → XR (Left.ce n) (Right.ce n)
  worlds : ∀ n → WR (Left.cw n) (Right.cw n)
  coordinates zero = coordinates-start
  coordinates (suc n) = add-coordinate (coordinates n) (advance (worlds n) (coordinates n))
  worlds zero = worlds-start
  worlds (suc n) = update worlds-start (coordinates (suc n))
  outputs : ∀ n → TR (Left.oo n) (Right.oo n)
  outputs n = emit (worlds n) (coordinates n)
  sums : ∀ n → TR (Left.oO n) (Right.oO n)
  sums zero = outputs zero
  sums (suc n) = add-output (sums n) (outputs (suc n))
```

XR/TR无需对全部raw树自反。实际实例在TwoSlot中给出。
