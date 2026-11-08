# 可数高度最高回调的完整无累加接口

这里比较同一合法公共高度hs B内的源旧种类与目标B。只请求原cl
产生的路径重建原种类；不要求任意路径证明无关。Typed零点是
原floor B，反馈无累加，区别于从1起步的对角链。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableTopIf where
open import Data.Nat using (ℕ; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
import OCF.Lean.GeneralOmegaSeededIf as Seed
open import OCF.Lean.FrozenWorldLift using (Same)

module At (B : Cd) (lB : LgB B) where
  module P = Seed.Prototype (F B) (floor B)
  callback : HB (F B) → HB (F B)
  callback a = observe (hs B) lB B (hsuc hself) (up a)
  record TopLaws : Set where
    field
      callback-typed : ∀ {a b} → Same a b → Same (callback a) (P.Typed b)
      coordinates : ∀ n → Same (iterate callback (floor B) n) (P.NoSum n)
      whole : Same (observe (hs B) lB B (hsuc hself) (floor (hs B)))
        (hl (λ n → P.NoSum (suc n)))
```

whole保留原完整最高节点输出，不能把其高层Same直接送进低层观察。
