# 原中槽到实际固定种子运行器的比较目标

read直接调用原Native.at，源/目标为同一字面界1下的1与0；没有新写
一个相似解释器。eval把加法重定位编码交给该实际运行器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseMiddleIf where
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid)
open import OCF.Align.BoundedWorldRebaseIf using (enc)
open import OCF.Align.BoundedWorldSeedIf using (Seed0; Seed1)

read : HB V → HB U
read a = at 1 0 (legal-num 1) hself (hsuc hself) a
eval : HB U → HB V → HB U
eval b a = read (enc b a)

record MiddleComparison : Set₁ where
  field
    native-seed : ∀ b a → Seed0 b → Seed1 a → Seed0 (eval b a)
    middle-bound : ∀ {a b u v} → Seed0 u → Seed0 v → Seed1 a → Seed1 b →
      Value (hs hz) a b → Value hz u v → Value hz (mid u a) (eval v b)
```

两个结论必须联立：实际新反馈坐标需要native-seed才能进入原Seed1
分支；反过来最低Ω的坐标恢复需要middle-bound。接口本身不作实例。
