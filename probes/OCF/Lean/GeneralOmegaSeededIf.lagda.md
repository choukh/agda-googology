# 原地板种子、无累加反馈的树侧原型

研究依据是旧typed折叠的树构造要求：零点为地板，后继为从0开始的
左加法迭代，旧Ω种类保留。本定义不导入记号。它不同于seed1的
Reify.Orbit，也不同于从首项开始的Affine.repeat；与原Level的精确桥
留给验收模块。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSeededIf where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)

module Prototype (S : KS) (seed : HB S) where
  leftMul : HB S → ℕ → HB S
  leftMul a zero = hz
  leftMul a (suc n) = a ⊞ leftMul a n
  Typed : HB S → HB S
  Typed hz = seed
  Typed (hs a) = hl (leftMul (Typed a))
  Typed (hl f) = hl (λ n → Typed (f n))
  Typed (hΩ κ g) = hΩ κ (λ e → Typed (g e))
  NoSum : ℕ → HB S
  NoSum zero = seed
  NoSum (suc n) = Typed (NoSum n)
  Sum : ℕ → HB S
  Sum zero = seed
  Sum (suc n) = Sum n ⊞ Typed (Sum n)
  whole : HB S
  whole = hl NoSum
  accumulated : HB S
  accumulated = hl Sum

  record Laws : Set where
    field
      noSum-legal : LgB seed → LgB whole
      sum-legal : LgB seed → LgB accumulated
      whole-cover : whole ≤ᵛ accumulated
      noSum-step : ∀ n {W : Wd S} → NoSum n ⊲[ W ] NoSum (suc n)
      sum-step : ∀ n {W : Wd S} → Sum n ⊲[ W ] Sum (suc n)
```

whole-cover是高层树值关系，不是新run的单调性。每个位置律明确在
同一W和右端公共树之下；准入后才能用某合法W接实际采样。
