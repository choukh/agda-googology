# 相邻标准塔的实际槽预算与输出

第四层。每个 k≥3 及每个 x≤sₖ，在 sₖ₊₁ 内同一真实第二塔运行可从 x 启动双重迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftStandard where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
import W4Block as W
import W4Path as P
open import WVOne using (T₀; read)
open import OCF.Align.Value using (_≼_; ≼-trans)
import B12Terminal as T
import B12ActualSlots as C
import B20Room as Room
import B20OldBlocks as Short
import B20StandardInside as Std
import Survey.W4IteratedLiftBlock as B
import Survey.W4IteratedLiftSlot as Slot
import Survey.W4IteratedLiftPlace as Place
import Survey.W4IteratedLiftSeries as S
import Survey.W4IteratedLiftRun as R
import Survey.W4IteratedLiftOrdinal as O
open T.Run

import Survey.W4IteratedLiftPay as Pay
import Survey.W4TowerLawStandard as Old

module Step (n : ℕ) where
  k = suc (suc (suc n))
  a = Std.std k
  b = Std.std (suc k)
  opaque
    all : ∀ i x → x ≼ a → O.stages (suc (suc i)) x ≼ b
    all = Pay.relative n (Old.Step.Q.Target.target n) (Old.Step.r n) Relation.Binary.PropositionalEquality.refl
      (Old.Step.Q.Target.covered n) (Old.Step.okay n) (Old.Step.cv n) (Place.Actual.series n) a b (Old.Step.Q.room n) (Old.Step.Q.into n)
```
