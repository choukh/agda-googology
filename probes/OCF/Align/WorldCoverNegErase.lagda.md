# 同一最高坐标不能擦除真实低槽

对冻结WorldCover接口的Original数组给出实际实例。两个完整合法世界
只有低槽不同，最高初坐标同为最低Ω地板；第零输出已有严格值差。
这里只否定把低槽统一替换成0的推理，不否定保留世界的输出模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldCoverNegErase where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; zz; same-value; same-sym)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.LHRecTy using (ls; lz)
open import OCF.Lean.LHRecFl using (Lg-flL)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor; floor-rel; pure-reflexive)
import OCF.Lean.Fold1 as Old
import OCF.Align.BoundedWorldCoverIf as W
import OCF.Align.BoundedWorldCoverRun
import OCF.Align.BoundedCompletionValueAcceptOld as O
import OCF.Align.BoundedCompletionValueAcceptPairStrength as P
import OCF.Align.FrozenOutputIf as I
import OCF.Align.FrozenAbsorbSeed as Seed

A : Cd
A = Old.TΩ1
W₀ W₁ : Wd (step (step S⊥))
W₀ = (tt , hz) , floor 0
W₁ = (tt , A) , floor 0
legal-W₀ : LgW (step (step S⊥)) W₀
legal-W₀ = (tt , tt) , Lg-flL (ls lz)
legal-W₁ : LgW (step (step S⊥)) W₁
legal-W₁ = (tt , Old.LgB-TΩ (hs hz) tt) , Lg-flL (ls lz)

module Zero = W.Actual (hs hz) tt W₀
module Raised = W.Actual (hs hz) tt W₁

same-initial : Same (Zero.Original.ce 0) (Raised.Original.ce 0)
same-initial = OCF.Align.BoundedWorldCoverRun.same-self (floor 0)

zero-output : Same (Zero.Original.oo 0) A
zero-output = O.fold-bridge (floor-rel 0) zz (floor 0)

module Strict = Seed.Seed (hs hz) (≤-refl (hs hz))
raised-output : hs A ≤ᵛ Raised.Original.oo 0
raised-output = ≤-trans (Strict.Orbit.strict-seed I.changing A)
  (≤-trans (same-value (P.run-bridge (floor-rel 0) (pure-reflexive A)))
    (same-value (same-sym (O.fold-bridge (floor-rel 0) (pure-reflexive A) (floor 0)))))

no-erase-lower-world : Raised.Original.oo 0 ≤ᵛ Zero.Original.oo 0 → ⊥
no-erase-lower-world p = ¬s≤ᵛ A
  (≤-trans raised-output (≤-trans p (same-value zero-output)))
```

所有前提给出实际合法世界与实际原始数组；比较的是完整第零输出树，
不是有限测试。此例不说Wi上的全族无法被新规范族覆盖，也不否定在
输出界中保留低槽信息的关系。最高坐标Same不足以替代该关系。
