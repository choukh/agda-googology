# 实际第二塔的第一正询问容纳整列块

第四层。对每个 i，把同一正询问中 i+2 个标准块的统一值律用于真实子运行。只需这座塔起初的正槽为标准 Ω。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextLiftStandard where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import W4Block as W
import W4Ops as O
import W4Path as P
open import WVOne using (T₀; read; 𝟏)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
import B12Terminal as T
import B12ActualSlots as C
import B15ReadPaths as R
import B15TowerIteration as Iter
import B20Room as Room
import B20StandardInside as Std
import Survey.W4NextLiftBlock as B
open T.Run

receive : ∀ i {l} (p : R.Reach (B.level (suc (suc i))) l) r → C.Covered r → B.op (suc (suc i)) 𝟏 ≼ read (T.value r)
receive i p r cv = ≼-trans {b = read (T.value local)}
  (B.all (suc (suc i)) local (Room.cover p r cv) 𝟏 (oneB local) (P.z≤ (B.level (suc (suc i))))) (Room.below p r cv)
  where local = Room.sub p r

module Run (r : T.Run (W.tw 2)) (eq : ok r ≡ P.Ok-tw 2) (cv : C.Covered r)
           (standard : proj₁ (bs r (W.tw 1) (W.ink W.self)) ≡ proj₁ (O.Ωt (W.tw 1))) where
  module Q = Iter.Tower.State 0 (λ u → u) L.zero r eq cv
  place : ∀ i → R.Reach (B.level (suc (suc i))) (W.tw 1 W.⊕ W.↑ (W.tw 1) (Q.C.ix 1))
  place i = subst (λ z → R.Reach (W.tw 1 W.⊕ W.iter (W._⊕ z) z (suc i)) (W.tw 1 W.⊕ W.↑ (W.tw 1) (Q.C.ix 1))) (cong (W.↑ (W.tw 1)) standard)
    (R.left (W.tw 1) (Q.at-index i))
  paid : ∀ i → B.op (suc (suc i)) 𝟏 ≼ read (T.value r)
  paid i = ≼-trans {b = read (T.value (Q.C.child 1))} (receive i (place i) (Q.C.child 1) (Q.C.cover cv 1)) (Q.C.lift-value 1)

opaque
  paid : ∀ i → B.op (suc (suc i)) 𝟏 ≼ Std.std 2
  paid = Run.paid (T.initial (W.tw 2) (P.Ok-tw 2)) refl (C.initial (W.tw 2) (P.Ok-tw 2)) refl
```
