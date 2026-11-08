# 原前缀反馈全部状态与打包输入的Seed证书

证书直接作用于既有Middle数组及PrefixPack.sourcePad；不替换轨道。
每个实际分支都包含当前坐标，并且中槽更新后仍满足Seed0。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedPrefix where
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf using (Value; vs)
open import OCF.Align.BoundedCompletionUniformClosure using (right-rel; up-value)
open import OCF.Align.BoundedWorldValueTwoSlot
open import OCF.Align.BoundedWorldSeedIf
open import OCF.Align.BoundedWorldSeedClosure
open import OCF.Align.BoundedWorldSeedMiddle using (preserve)
import OCF.Align.BoundedWorldPrefixIf as If
import OCF.Align.BoundedWorldPrefixPack as Pack

module Prefix (u : Cd) (b : HB U) (p : HB V) (sb : Seed0 b) (sp : Seed1 p) where
  module M = If.Middle u b p
  module Packed = Pack.Pack u b p (self0 sb) (self1 sp)
  coordinates : ∀ n → Seed0 (M.ce n)
  advance : ∀ n → Seed0 (mid (M.cw n) (p ⊞ up (M.ce n)))
  coordinates zero = sb
  coordinates (suc n) = add0 (coordinates n) (advance n)
  advance zero = preserve sb (add1 sp (up1 sb))
  advance (suc n) = preserve (coordinates (suc n)) (add1 sp (up1 (coordinates (suc n))))

  branches : ∀ n → Seed1 (p ⊞ up (M.ce n))
  branches n = add1 sp (up1 (coordinates n))
  branch-recovers : ∀ n → Value (hs hz) (up (M.ce n)) (p ⊞ up (M.ce n))
  branch-recovers n = right-rel p (up-value hz (self0 (coordinates n)))

  sourcePad : ∀ n → Seed1 (Packed.sourcePad n)
  sourcePad zero = branches zero
  sourcePad (suc n) = add1 (sourcePad n) (vs (self1 (branches (suc n))) , branches (suc n))

open import OCF.Align.BoundedWorldSeedActual using (old1-coordinates)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedNativeValueFirst as First

module Actual k = Prefix First.feedback (floor zero) (Whole.Model.ce k) floor0 (old1-coordinates k)

actual-coordinate : ∀ k n → Seed0 (If.Middle.ce First.feedback (floor zero) (Whole.Model.ce k) n)
actual-coordinate k = Actual.coordinates k
actual-sourcePad : ∀ k n → Seed1 (Actual.Packed.sourcePad k n)
actual-sourcePad k = Actual.sourcePad k
```

k=1即真实floor1⊞act floor1前缀，底槽为非零feedback；实际上k全族
均已实例化。坐标可由分支输入在值关系中恢复，尚不意味着动态low能
被固定seed的Uniform输出吸收；这个值覆盖仍需独立证明。
