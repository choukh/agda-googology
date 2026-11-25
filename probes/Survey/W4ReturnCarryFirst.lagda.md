# 首座正塔选择的独立重置已经支付 h 不动点

第四层，无条件。首塔的全部零槽有共同下界 s 时，第 n+1 个真实下标上的独立重置，覆盖 h 从 s+1 开始迭代 n+1 次的值。两层上方实际塔的每个后继阶段都能使用这一事实。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCarryFirst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l; l≼)
import W4Block as W
import W4Ops as O
import W4Fold as F
import W4Path as P
open import WVOne using (read; T₀; ≼-+ˡ; h₁)
import B12Terminal as T
import B12ActualSlots as C
import B14Tower as V
import B20Room as R
import B21TowerPorts as Port
import Survey.W4RoomHeight as Height
import Survey.W4RoomDerivative as D
import Survey.W4RoomDiagonal as G
import B20OldStage as St
import Survey.W4FourthLiftValue as I
import Survey.W4ReturnCarry as Carry
open T.Run

same : ∀ t → ok t ≡ P.Ok-tw 1 → ∀ n → V.At.idx t n ≡ Port.At.index 0 (bs t) (O.Ωt W.zero) n
same (T.makeRun _ _ _ _ _ _) refl n = refl

module At (r : T.Run (W.tw 1)) (eq : ok r ≡ P.Ok-tw 1) (cv : C.Covered r) (s : T₀) (high : R.Room r s) (x : T₀) where
  module Payout = Carry.At.Orbit 0 (bs r) x
  module Z = D.At r cv s high

  branch : ∀ n → I.h (D.chain s n) ≼ Payout.unit (suc n)
  branch n = fit (Payout.A.index (suc n))
    (subst (λ z → G.H.cut (D.chain s n) ≼ read z) (same r eq (suc n)) (Z.budget n))
    where
    fit : ∀ z → G.H.cut (D.chain s n) ≼ read z →
      I.h (D.chain s n) ≼ read (proj₁ (F.ψ₀ (h₁ z) (proj₂ (P.Ok-tw 1) z) (proj₁ (O.Ωt (h₁ z)))))
    fit z d = ≼-trans (≼-+ˡ G.three (I.h (D.chain s n))) (≼-trans (G.buffer (D.chain s n) WVOne.𝟏)
      (G.H.apply (D.chain s n) z d t (C.initial (h₁ z) (ok t)) WVOne.𝟏 (oneB t) (P.z≤ _)))
      where t = T.initial (h₁ z) (proj₂ (P.Ok-tw 1) z)

  into : ∀ n → Payout.unit n ≼ Payout.budget
  into zero = ≼l 0 (≼-+ˡ x (Payout.unit 0))
  into (suc n) = ≼l (suc n) (≼-trans (≼-+ˡ x (Payout.unit (suc n))) (≼-+ˡ (Payout.total n) (x L.+ Payout.unit (suc n))))
  full : D.next s ≼ Payout.budget
  full = l≼ λ { zero → ≼-trans (D.inflation (L.suc s)) (≼-trans (branch 0) (into 1))
              ; (suc n) → ≼-trans (branch n) (into (suc n)) }

module Stage (r : T.Run (W.nd W.sS (λ _ → W.tw 1))) (eq : proj₂ (ok r) tt ≡ P.Ok-tw 1) (cv : C.Covered r)
             (x : T₀) (high : R.Room r x) where
  module A = Carry.At.Carry 0 r eq cv x high
  module K = St.At (W.sΩ W.zero) h₁ r cv
  start : R.Room K.r₀ x
  start w = high (W.inc tt w)
  stages : ∀ n w → W.iter D.next x (suc n) ≼ read (proj₁ (K.S n W.zero w))
  stages zero w = ≼-trans (D.law (V.reset K.r₀ (bs K.r₀ W.zero w) (oneB K.r₀ w)) K.sub-covered x start w) (K.weaken _ w _)
  stages (suc n) w = ≼-trans (D.law (V.reset t (bs t W.zero w) (oneB t w)) (K.cover n) _ (stages n) w) (K.weaken _ w _)
    where t = A.J.F.snap n

  refill : ∀ n → W.iter D.next x (suc n) ≼ A.reserve n
  refill zero = At.full K.r₀ eq K.sub-covered x start x
  refill (suc n) = At.full (A.J.F.snap n) eq (K.cover n) (W.iter D.next x (suc n)) (stages n) (A.reserve n)

  carry : ∀ n u → R.Room (A.Selected.target n u) (W.iter D.next x (suc n))
  carry n u w = ≼-trans (refill n) (A.Selected.common n u w)
```
