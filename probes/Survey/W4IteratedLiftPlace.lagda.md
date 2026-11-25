# 把含整列正块的槽定位到相邻标准塔中的第二塔

第四层。对任意 k≥3，下一座标准塔内部实际第二塔上的指定正槽具有整列累计的形状。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftPlace where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong)
import W4Block as W
import WVOne
import B12Terminal as T
import B20Room as Room
import B20OldBlocks as Short
import Survey.W4TowerLawStandard as Standard
import Survey.W4IteratedLiftBlock as B
import Survey.W4IteratedLiftSlot as Slot
import Survey.W4IteratedLiftCapture as Cap
open T.Run

select : ∀ n (r : T.Run (W.tw (suc (suc n)))) → (∀ u → Slot.Series (proj₁ (bs r B.k u))) →
  Slot.Series (proj₁ (bs (Room.sub (Short.toward n) r) B.k (W.ink W.self)))
select n r h = subst Slot.Series (sym (cong proj₁ (Cap.pull n r B.k (W.ink W.self)))) (h (Cap.path n (W.ink W.self)))

module Actual (n : ℕ) where
  module Q = Standard.Step n
  module U = Q.Q
  module S = Cap.Start (suc (suc n)) U.Location.found U.Location.cert (Room.cover U.Location.path U.Location.one U.Location.oc)
    WVOne.𝟏 U.ARun.room U.core
  opaque
    series : Slot.Series (proj₁ (bs Q.r B.k (W.ink W.self)))
    series = select n U.Target.target S.at
```
