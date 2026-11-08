# 原反馈链的完成前缀接口

这里只运输原chain每步的左前缀，不声称leg保持一般第一位置或值序。
这一差别让实际采样能共享较后链点的字面界，又不重证全局比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaLegPrefixIf where
open import Data.Nat using (suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.BoundedFoldRun using (chain)

record PrefixLaw : Set where
  field
    complete-prefix : ∀ a b → leg a ⊲ leg (a ⊞ b)
    sample-step : ∀ (H : Cd → Cd) n → leg (chain H n) ⊲ leg (chain H (suc n))
```

complete-prefix的两树由同一个a和右加数b给出；sample-step是其原算法
实例。没有对任意两个裸下标给顺序或判等操作。
