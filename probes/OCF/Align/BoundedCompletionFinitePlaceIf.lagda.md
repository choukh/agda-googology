# 原source跨组件注入的接口

比较的是原ι的两处注入，不是新source或复制后的θ。
源高度n与n+1在右公共界有后继路径；两次目标比较各带自己的合法界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceIf where
open import Data.Nat using (suc)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf

record PlacementBridge : Set₁ where
  field
    coherent-up : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
      (pc : num n ⊲ B) (pc′ : num (suc n) ⊲ B′)
      (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
      {a b} → Rel (num n) a b →
      Rel (num m) (at n m lB pc pt a)
        (at (suc n) m lB′ pc′ pt′ (up b))
```

字段待原运行器的实际证明实现，不是条件定理的前提。
