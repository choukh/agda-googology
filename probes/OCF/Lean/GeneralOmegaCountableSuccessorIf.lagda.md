# 原可数后继高度的完整反馈公式

本篇只用树侧原定义。最高Ω在目标0上可能落入same或above：B=0
是same，B为后继或ℕ极限是above。公式保留这两个真实分派的共同
反馈结果，不把一般kind分类当作相同，也不改变累计地板。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableSuccessorIf where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)

module At (B : Cd) (lB : LgB B) where
  module P = Prototype (F B) (floor B)
  callback : HB (F B) → HB (F B)
  callback a = observe (hs B) lB B (hsuc hself) (up a)
  coordinates : ℕ → HB (F B)
  coordinates = iterate callback (floor B)
  emit : HB (F B) → Cd
  emit a = observe (hs B) lB hz (hsuc (z⊲ᴮ B)) (up a)
  read-orbit : ℕ → Cd
  read-orbit i = observe B lB hz (z⊲ᴮ B) (P.NoSum i)

root : ∀ B lB → observe (hs B) lB hz (hsuc (z⊲ᴮ B)) (floor (hs B)) ≡
  hl (λ i → At.emit B lB (At.coordinates B lB i))
root hz lB = refl
root (hs B) lB = refl
root (hl f) lB = refl
root (hΩ () f) lB
```

root只展开原完整轨道；尚未把coordinates与NoSum互换，更没有
声称Γ单调。后续互换必须依赖实际typed回调和遗传关系的跨up定理。
