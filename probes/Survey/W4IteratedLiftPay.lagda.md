# 相邻标准塔的实际槽预算与输出

第四层。每个 k≥3 及每个 x≤sₖ，在 sₖ₊₁ 内同一真实第二塔运行可从 x 启动双重迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftPay where

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

enclose : (r : T.Run (W.tw 2)) → ok r ≡ P.Ok-tw 2 → C.Covered r → Slot.Series (proj₁ (bs r B.k (W.ink W.self))) →
  ∀ (a b : T₀) → Room.Room r a → read (T.value r) ≼ b → ∀ i x → x ≼ a → O.stages (suc (suc i)) x ≼ b
enclose r eq cv s a b high into i x d = ≼-trans {a = O.stages (suc (suc i)) x} {b = read (T.value r)} {c = b}
  (Z.Place.paid i x (λ w → ≼-trans {a = x} {b = a} d (high w))) into
  where module Z = R.Run r eq cv S.jump (S.transfer s)

relative : ∀ n (t : T.Run (W.tw (suc (suc n)))) (r : T.Run (W.tw 2)) → r ≡ Room.sub (Short.toward n) t →
  C.Covered t → ok r ≡ P.Ok-tw 2 → C.Covered r → Slot.Series (proj₁ (bs r B.k (W.ink W.self))) →
  ∀ (a b : T₀) → Room.Room t a → read (T.value t) ≼ b → ∀ i x → x ≼ a → O.stages (suc (suc i)) x ≼ b
relative n t ._ Relation.Binary.PropositionalEquality.refl c eq cv series a b high more =
  enclose r eq cv series a b (Room.room (Short.toward n) t {v = a} high)
    (≼-trans {a = read (T.value r)} {b = read (T.value t)} {c = b} (Room.below (Short.toward n) t c) more)
  where r = Room.sub (Short.toward n) t

```
