# 从旧链读值到 W4 的单次内部反馈

> 第四层。保留 ω 层各前缀实际更新过的槽。初值严格低于指定有限 Ω 层时，经典地，达到该层等价于内部反馈覆盖它的每个严格前驱。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LegacyFeedback where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; s≼s; l≼; ≼l)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import OCF.Lean.YiRVLevel using (LEM)
open import WVOne using (read; T₀; 𝟏)
import W4Block as W
import W4Ops as Op
import W4Fold as F
import W4Path as Path
import WKTower as WT
import B12Terminal as T
import B12TerminalSrc as TS
import B12ActualSlots as Slots
import B12Strict as Strict
import B13FiniteLift as Lift
import B13FiniteTower as Lev
import B17ValueDich as Compare
import B18Product as P
import B19IdealProduct as I
import B31Head as Head
import B31UProduct as Product
import B12BtboCut as C
import B27RunCut as Cuts
import Survey.W4FiniteOmegaCut as Finite

child : ℕ → W.L
child zero = W.zero
child (suc n) = WT.gL n
level : ∀ n → WT.gL n ≡ Lift.sc (child n)
level zero = refl
level (suc n) = Lev.succ-level n

module Run (r : T.Run WT.Lω) where
  module A = Product.Run WT.gL r
  seat : ∀ i → T.Run (Lift.sc (child i))
  seat = λ n → subst T.Run (level n) (A.part n)
  module Cell (i : ℕ) = Head.Cell (child i) (seat i)
  leaf : ℕ → ℕ → T₀
  leaf = λ i j → Cell.leaf i j
  same-unit : ∀ i → Product.fold₁ (seat i) ≡ A.unit i
  same-unit i = cast (level i) (A.part i)
    where
    cast : ∀ {k k′} (e : k ≡ k′) (t : T.Run k) → Product.fold₁ (subst T.Run e t) ≡ Product.fold₁ t
    cast refl _ = refl

  into : ∀ i j → leaf i j ≼ read (T.value r)
  into i j = ≼-trans {b = A.unit i} (subst (leaf i j ≼_) (same-unit i) (Cell.into i j))
    (≼-trans {b = A.seed i P.· A.unit i} (P.pad (T.Run.oneβ (A.part i)) (A.unit i))
      (≼-trans {b = A.term i} (proj₂ (A.scale i)) (T.lim-child WT.gL r i)))

  Hit : T₀ → Set
  Hit x = Σ ℕ (λ i → Σ ℕ (λ j → L.suc x ≼ leaf i j))

  module Test (n : ℕ) (start : Finite.At.small n A.start) where
    module K = Finite.At n
    cap : (x : T₀) → K.small x → (∀ i j → leaf i j ≼ x) → K.small (read (T.value r))
    cap x sx all = ≼-trans {b = L.suc (A.start P.· I.power u L.ωᶜ)} (s≼s budget)
      (K.product A.start (I.power u L.ωᶜ) start (K.power u L.ωᶜ inside K.omega))
      where
      u = (x P.· L.ωᶜ) P.· L.ωᶜ
      inside : K.small u
      inside = K.product (x P.· L.ωᶜ) L.ωᶜ (K.product x L.ωᶜ sx K.omega) K.omega
      units : ∀ i → A.unit i ≼ u
      units i = subst (_≼ u) (same-unit i) (Cell.cap i x (all i))
      budget : read (T.value r) ≼ (A.start P.· I.power u L.ωᶜ)
      budget = A.Budget.whole u units

    collect : (∀ x → K.small x → Hit x) → K.q ≼ read (T.value r)
    collect hits = Cuts.predecessors K.q (read (T.value r)) λ x sx →
      let i , j , h = hits x sx in ≼-trans {b = leaf i j} h (into i j)

    module Classical (lem : LEM) where
      extract : K.q ≼ read (T.value r) → ∀ x → K.small x → Hit x
      extract h x sx with lem (Hit x)
      ... | inj₁ yes = yes
      ... | inj₂ no = ⊥-elim (s≼-irrefl K.q (≼-trans {b = L.suc (read (T.value r))} (s≼s h) (cap x sx all)))
        where
        all : ∀ i j → leaf i j ≼ x
        all i j with Compare.Classical.compare lem (leaf i j) x
        ... | inj₁ le = le
        ... | inj₂ gt = ⊥-elim (no (i , j , gt))

module First (s : W.Sh) (g : W.Ch s → W.L) (r : T.Run (Lift.sc (W.nd s g))) (cv : Slots.Covered r) where
  k = W.nd s g
  module H = Head.Cell k r
  sub : T.Run k
  sub = T.makeRun H.o H.B (Op.Ωt W.zero) (λ w → T.Run.oneB r (W.inc tt w))
    (λ w → T.Run.omegaB r (W.inc tt w)) (≼-refl 𝟏)
  covered : Slots.Covered sub
  covered i w = cv i (W.inc tt w)
  strict : L.suc (read (T.value sub)) ≼ H.leaf 1
  strict = Strict.strict (F.mono k H.o H.B W.zero (Path.z≤ k) (Op.Ωt W.zero) before)
    where
    before : W._⊢_◃_ k (proj₁ (Op.Ωt k)) (H.state 1)
    before with cv k (W.inc tt W.self)
    ... | inj₁ eq = subst (λ t → W._⊢_◃_ k t (H.state 1)) (sym eq) W.◃e
    ... | inj₂ d = W.◃t d W.◃e

module Live = Run TS.middle
module Two = First W.sS _ (T.finiteRun 2) (Slots.all-finite 2)
module Three = First W.sS _ (T.finiteRun 3) (Slots.all-finite 3)

import B18OrbitRows as Rows
import B19IdealRow as Ref

live-two : L.suc (C.finite 2) ≼ Live.leaf 2 1
live-two = ≼-trans {b = L.suc (read (T.value Two.sub))} (s≼s (T.anchor₂ Two.sub)) Two.strict

live-row : L.suc Ref.row ≼ Live.leaf 3 1
live-row = ≼-trans {b = L.suc (read (T.value Three.sub))} (s≼s (Rows.At.whole Three.sub Three.covered)) Three.strict

import B18ResetCellGoal as Seed
open import OCF.Align.Value using (≺→s≼)
open import OCF.Align.BTBOFullV3 using (Fstep)

live-start : ∀ n → Finite.At.small n Live.A.start
live-start n = ≼-trans {b = L.suc L.ωᶜ} (s≼s (proj₁ Seed.First.omega)) (Finite.At.omega n)
module LiveCut (n : ℕ) = Live.Test n (live-start n)

step : ∀ n → L.suc (C.finite n) ≼ C.finite (suc n)
step n = ≺→s≼ {c = C.finite n} {b = C.finite (suc n)} (Fstep (L.natᴵ n))

module Ladder (r : T.Run WT.Lω) (tiny : ∀ n → Finite.At.small n (Product.Run.start WT.gL r)) where
  module X = Run r
  All = ∀ n → X.Hit (C.finite n)
  sufficient : All → C.omega-cut ≼ read (T.value r)
  sufficient pay = l≼ λ n → let i , j , h = pay n in
    ≼-trans {b = L.suc (C.finite n)} (≼-suc (≼-refl _)) (≼-trans {b = X.leaf i j} h (X.into i j))

  necessary : LEM → C.omega-cut ≼ read (T.value r) → All
  necessary lem paid n = X.Test.Classical.extract n (tiny n) lem
    (≼-trans {b = C.omega-cut} (≼l (suc (suc n)) (≼-refl _)) paid) (C.finite n)
    (≼-trans {b = C.finite (suc n)} (step n) (≼-trans {b = L.suc (C.finite (suc n))} (≼-suc (≼-refl _)) (step (suc n))))

module Actual = Ladder TS.middle live-start
module Ordinary = Ladder (T.tower-child TS.standard 1) Finite.At.one
```
