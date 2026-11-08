# 原世界最高坐标的统一消去

定理对任意合法层号及任意完整世界成立，不仅有限自然数层号。
原因是输入 up a 不含最高新种类，而目标恰为其直接前层；所有分支
确实保留，故本定理没有丢掉一次会被执行的低层坍缩。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldCoverRun where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.FrozenInnerOuter using (same-add; same-mul)
import OCF.Lean.Fold1Fold as F
open import OCF.Align.BoundedWorldCoverIf

same-self : ∀ {S} (a : HB S) → Same a a
same-self hz = zz
same-self (hs a) = ss (same-self a)
same-self (hl f) = ll (λ n → same-self (f n))
same-self (hΩ κ g) = oo (λ e → same-self (g e))

coordinate : ∀ m lm W {a b} → Same a b →
  Same (F.Φ (hs m) lm m (hsuc hself) W (up a)) (act b)
coordinate m lm W zz = ss zz
coordinate m lm W (ss p) = ll (same-mul (coordinate m lm W p))
coordinate m lm W (ll p) = ll (λ n → coordinate m lm W (p n))
coordinate m lm W (oo p) = oo (λ e → coordinate m lm W (p e))

coordinates : ∀ m lm W n → Same (Actual.Original.ce m lm W n)
  (Actual.orbit m lm W n)
coordinates m lm W zero = same-self _
coordinates m lm W (suc n) = same-add (coordinates m lm W n)
  (coordinate m lm (Actual.Original.cw m lm W n) (coordinates m lm W n))

instance-highest : HighestSimulation
instance-highest = record
  { coordinate = coordinate
  ; coordinates = coordinates
  ; lower-world = λ m lm W → λ { zero → refl ; (suc n) → refl } }
```

这没有使用坐标分支函数对 Same 的额外同余假设：本步全部 keep，Same 的
Ω 构造子只需相同坐标逐点比较。下一步降到较低目标会发生真实坍缩，
不能沿用这个理由省掉异坐标同余或低槽世界关系。
