# 真实有限最高反馈的初界覆盖接口

Old.Wi的初界是低层top，不是纯seed1。本接口不假定seed1已支配它，
而要求实际model前缀在第一次反馈后供给同类型地板。层对n、n+1
使用字面后继公共界；值比较针对该回灌坐标，不作裸下标判定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueIf where
open import Data.Nat using (suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ

coordinate : ∀ n → HB (Native (num n)) → HB (Native (num n))
coordinate n c = at (suc n) n {B = num (suc n)} (legal-num (suc n)) hself (hsuc hself)
  (up (Θ.model n) ⊞ up c)

first : ∀ n → HB (Native (num n))
first n = chain (coordinate n) 1

record FirstFloor : Set where
  field
    first-floor : ∀ n → floor n ≤ᵛ first n
```

FirstFloor目前仅列明待证的真实全n义务，不假定已实例化。
它也不是Old全反馈轨道下界：后续仍需比较Old的世界更新与本运行器。
