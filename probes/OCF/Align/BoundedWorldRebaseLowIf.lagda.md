# 双槽可数输出到实际重定位运行器的比较

保留原low的动态底槽和中槽，目标依次使用原Native.at与原terminal。
此接口不假定两者复合等于low。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseLowIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldSeedIf using (Seed0; Seed1)
open import OCF.Align.BoundedWorldValueTwoSlot using (low)
open import OCF.Lean.RebaseMiddleIf using (eval)
import OCF.Align.BoundedNativeTerminalReady as T

record LowerComparison : Set₁ where
  field
    lower : ∀ {a b u v x y} → Seed0 u → Seed0 v → Seed1 a → Seed1 b →
      Value (hs hz) a b → Value hz u v → x ≤ᵛ y →
      low x u a ≤ᵛ T.fold y (eval v b)
```
