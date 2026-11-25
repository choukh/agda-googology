# 继承零槽的第二塔可任意次使用同一个升层律

第四层。把第二塔第一正询问里的每个有限重复块用于同一真实输入。正槽树及其能实现的升层变换都作为结构参数，允许每次转移时选用更强的实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftRun where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
import W4Block as W
import W4Path as P
open import WVOne using (T₀; read; h₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
import B12Terminal as T
import B12ActualSlots as C
import B15TowerIteration as Iter
import B15ReadPaths as R
import B20Room as Room
import B20StandardInside as Std
import Survey.W4RoomDerivative as D
import Survey.W4RoomHeight as H
import Survey.W4NextLiftIndex as I
import Survey.W4IteratedLiftBlock as B
open T.Run

Op = T₀ → T₀
Transfer : B.Tr → (Op → Op) → Set
Transfer t F = ∀ p → B.Nonzero (I.plug p W.zero) → ∀ f → H.Law (I.plug p W.zero) f → H.Law (I.plug p (B.readL t)) (F f)
positive : ∀ {t} → B.Positive t → Transfer t H.repeat
positive p e nz f u = B.raise p [] e nz u

module Run (r : T.Run (W.tw 2)) (eq : ok r ≡ P.Ok-tw 2) (cv : C.Covered r) (F : Op → Op)
  (raise : Transfer (proj₁ (bs r B.k (W.ink W.self))) F) where
  module Q = Iter.Tower.State 0 (λ u → u) L.zero r eq cv
  tiles = W.iter (W._⊕ Q.w) Q.w
  level : ℕ → W.L
  level zero = B.k
  level (suc n) = B.k W.⊕ tiles n
  op = W.iter F D.next
  base-nz = B.node (W.sΩ W.zero) h₁
  all : ∀ n → H.Law (level n) (op n)
  all zero = D.law
  all (suc zero) = raise (B.k ∷ []) base-nz D.next D.law
  all (suc (suc n)) = raise (tiles n ∷ B.k ∷ []) (B.live (B.k ∷ []) base-nz (tiles n)) (op (suc n)) (all (suc n))
  module Place (i : ℕ) where
    child = Q.C.child 1
    cc = Q.C.cover cv 1
    path = R.left B.k (Q.at-index i)
    sub = Room.sub path child
    paid : ∀ x → Room.Room r x → op (suc (suc i)) x ≼ read (T.value r)
    paid x hi = ≼-trans {b = read (T.value sub)}
      (all (suc (suc i)) sub (Room.cover path child cc) x (Room.room path child (λ v → hi (W.inc (Q.C.ix 1) v))) (P.z≤ (level (suc (suc i)))))
      (≼-trans {b = read (T.value child)} (Room.below path child cc) (Q.C.lift-value 1))
```
