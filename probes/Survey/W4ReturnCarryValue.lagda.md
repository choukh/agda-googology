# 第三、第四座实际塔对更新后的反馈合计取不动点

第四层，无条件。对任意实际时刻和所选正分支，第三塔内的首塔调用对全部继承槽的共同下界取上方首个 h 不动点，第四塔内的第二塔调用把该操作迭代任意有限次。由同一塔的读值容纳全部时刻。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCarryValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; l≼; z≼)
import W4Block as W
import W4Path as P
open import WVOne using (read; T₀)
import B12Terminal as T
import B12ActualSlots as C
import B14Tower as V
import B20Room as Room
import Survey.W4RoomDerivative as D
import Survey.W4ReturnCarry as R
open T.Run

module First (r : T.Run (W.tw 3)) (eq : ok r ≡ P.Ok-tw 3) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
  module A = R.At.Actual 1 r eq cv x high
  reserve = A.Use.reserve
  run = A.Use.Selected.target
  every : ∀ n u w → D.next (reserve n) ≼ V.valueAt (run n u) w
  every n u = D.law (run n u) (A.Use.Selected.covered n u) (reserve n) (A.Use.Selected.common n u)
  selected : ∀ n u → D.next (reserve n) ≼ read (T.value r)
  selected n u = ≼-trans {b = read (T.value (run n u))} (every n u (P.z≤ _)) (A.into n u)
  all : L.lim (λ n → D.next (reserve n)) ≼ read (T.value r)
  all = l≼ (λ n → selected n n)

module Second (r : T.Run (W.tw 4)) (eq : ok r ≡ P.Ok-tw 4) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
  module A = R.At.Actual 2 r eq cv x high
  reserve = A.Use.reserve
  run = A.Use.Selected.target
  selected : ∀ n u → D.block (reserve n) ≼ read (T.value (run n u))
  selected n u = D.Second.block-in (run n u) (A.Use.Selected.standard n u) (A.Use.Selected.covered n u)
    (reserve n) (A.Use.Selected.common n u)
  all : L.lim (λ n → D.block (reserve n)) ≼ read (T.value r)
  all = l≼ λ n → ≼-trans {b = read (T.value (run n n))} (selected n n) (A.into n n)

module Actual (m : ℕ) where
  r = T.limRun W.tw T.terminal m
  cv = C.enter W.sL W.tw T.terminal m (T.prefix W.tw m) (C.initial W.Λ P.Ok-Λ)
  low : Room.Room r L.zero
  low w = z≼

module Third = First (Actual.r 3) refl (Actual.cv 3) L.zero (Actual.low 3)
module Fourth = Second (Actual.r 4) refl (Actual.cv 4) L.zero (Actual.low 4)
```
