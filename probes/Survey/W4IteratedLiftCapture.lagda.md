# 相邻标准塔中可重启的第二塔运行

第四层。由实际更新的标准起点和所用树的证书求出槽的准确形状。沿后续的第零孩子下行不会再次改写该槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftCapture where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
open import WVOne using (T₀)
import B12Terminal as T
import B12ActualSlots as C
import B13FiniteLift as Succ
import B15ReadPaths as R
import B20Room as Room
import B20OldBlocks as Short
import Survey.W4TowerLawStandard as Standard
import Survey.W4ReturnCarry as Carry
import Survey.W4IteratedLiftBlock as B
import Survey.W4IteratedLiftSlot as Slot
open T.Run

module Start (m : ℕ) (r : T.Run (Succ.sc (W.tw (suc m)))) (o : proj₂ (ok r) tt ≡ P.Ok-tw (suc m)) (cv : C.Covered r)
             (x : T₀) (high : Room.Room r x) (fresh : bs r ≡ F.B₀ _) where
  module S = Carry.At.Carry m r o cv x high
  mid = W.tw (suc m)
  base : bs S.M.r₀ ≡ F.B₀ mid
  base = Standard.stay Standard.child r fresh
  tree : S.M.c ≡ proj₁ (O.Ωt mid)
  tree = cong (λ b → proj₁ (b mid (W.inc tt W.self))) fresh
  found = S.Selected.target 0 0
  at : (u : B.k W.≤ W.tw m) → Slot.Series (proj₁ (bs found B.k u))
  at u = Slot.Form.form m (ok S.M.r₀) o (bs S.M.r₀) base S.M.c tree u

path : ∀ n {k} → k W.≤ W.tw 2 → k W.≤ W.tw (suc (suc n))
path zero w = w
path (suc n) w = W.inc W.zero (path n w)
pull : ∀ n r j w → bs (Room.sub (Short.toward n) r) j w ≡ bs r j (path n w)
pull zero r j w = refl
pull (suc n) r j w = pull n (Room.sub R.omega r) j w

```
