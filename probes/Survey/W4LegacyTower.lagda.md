# 整棵 W4 严格越过有限层上确界的单塔判据

> 第四层。ψ₀(Ω_ω) < |W4| 当且仅当同一座正塔内的单位反馈返回严格越过每个有限 Ω 层。取出塔号用排中律，由见证得到下界无条件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LegacyTower where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _≤′_; ≤′-reflexive; ≤′-step; _⊔_)
import Data.Nat.Properties as N
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; ≼lim⁻)
open import OCF.Lean.YiRVLevel using (LEM)
open import WVOne using (T₀; 𝟏)
import B12BtboCut as C
import B12EboRows as Rows
import B18Product as P
import B18Reset as R
import B18ResetCell as Cell
import B19Coefficient as Product
import B26PActual as W
import B26PBounds as Budget
import B26PSums as Sums
import B27RunCut as Cut
import Survey.W4FiniteOmegaCut as Ar
import Survey.W4LegacyFeedback as Local

module Threshold (q : T₀) (one : L.suc 𝟏 ≼ q) (omega : L.suc L.ωᶜ ≼ q)
  (mul : ∀ x y → L.suc x ≼ q → L.suc y ≼ q → L.suc (x P.· y) ≼ q) where
  f = Cell.At.fresh
  Cap = λ n → Σ T₀ (λ x → L.suc x ≼ q × (∀ j → f n j ≼ x))
  Cofinal = λ n → (x : T₀) → L.suc x ≼ q → Σ ℕ (λ j → L.suc x ≼ f n j)

  bounded : (∀ n → Cap n) → W.Y ≼ q
  bounded caps = ≼-trans {b = L.lim (λ n → R.product (suc n))} (proj₁ Product.terminal)
    (l≼ λ n → ≼-trans {b = L.suc (R.product (suc n))} (≼-suc (≼-refl _)) (prefix (suc n)))
    where
    unit : ∀ n → L.suc (R.fresh n) ≼ q
    unit zero = ≼-trans {b = L.suc L.ωᶜ} (s≼s (proj₁ B18ResetCellGoal.First.omega)) omega
      where import B18ResetCellGoal
    unit (suc n) with caps n
    ... | x , small , all = ≼-trans {b = L.suc (x P.· L.ωᶜ)}
      (s≼s (≼-trans {b = WVOne.Mv x 𝟏} (Cell.At.bound n x all) (Budget.one-step x))) (mul x L.ωᶜ small omega)
    prefix : ∀ n → L.suc (R.product n) ≼ q
    prefix zero = one
    prefix (suc n) = mul (R.product n) (R.fresh n) (prefix n) (unit n)

  necessary : LEM → L.suc q ≼ W.Y → Σ ℕ Cofinal
  necessary lem = Cut.Choice.witness q W.Y f lem bounded

  sufficient : ∀ n → Cofinal n → L.suc q ≼ W.Y
  sufficient n co = ≼-trans {b = L.suc (Rows.child (suc n))} (s≼s (≼-trans {b = R.fresh (suc n)}
    (Cut.predecessors q (R.fresh (suc n)) λ x sx → let j , h = co x sx in
       ≼-trans {b = f n j} h (Cell.At.into n j)) (R.lower (suc n)))) (Sums.child-in (suc n))

module Finite (n : ℕ) = Threshold (Ar.At.q n) (Ar.At.one n) (Ar.At.omega n) (Ar.At.product n)

raise : ∀ i j → i ≤ j → C.finite i ≼ C.finite j
raise i j d = along (N.≤⇒≤′ d)
  where
  along : ∀ {x} → i ≤′ x → C.finite i ≼ C.finite x
  along (≤′-reflexive refl) = ≼-refl _
  along (≤′-step {n = x} d) = ≼-trans {b = L.suc (C.finite x)} (≼-suc (along d)) (Local.step x)

small : (x : T₀) → L.suc x ≼ C.omega-cut → Σ ℕ (λ k → L.suc x ≼ C.finite k)
small x = ≼lim⁻ {a = x} {f = C.finite}

times : ∀ x y → L.suc x ≼ C.omega-cut → L.suc y ≼ C.omega-cut → L.suc (x P.· y) ≼ C.omega-cut
times x y hx hy with small x hx | small y hy
... | i , a | j , b = ≼l {f = C.finite} (suc (suc m)) (Ar.At.product m x y
  (≼-trans {b = C.finite i} a (raise i (suc (suc m)) (N.m≤n⇒m≤1+n (N.m≤n⇒m≤1+n (N.m≤m⊔n i j)))))
  (≼-trans {b = C.finite j} b (raise j (suc (suc m)) (N.m≤n⇒m≤1+n (N.m≤n⇒m≤1+n (N.m≤n⊔m i j))))))
  where m = i ⊔ j

module Limit = Threshold C.omega-cut (≼l {f = C.finite} 2 (Ar.At.one 0))
  (≼l {f = C.finite} 2 (Ar.At.omega 0)) times

SameTower : Set
SameTower = Σ ℕ (λ n → ∀ k → Σ ℕ (λ j → L.suc (C.finite k) ≼ Cell.At.fresh n j))

extract : LEM → L.suc C.omega-cut ≼ W.Y → SameTower
extract lem greater = let n , co = Limit.necessary lem greater in n , λ k → co (C.finite k) (≼l {f = C.finite} (suc k) (Local.step k))

collect : SameTower → L.suc C.omega-cut ≼ W.Y
collect (n , witness) = Limit.sufficient n co
  where
  co : Limit.Cofinal n
  co x sx = let k , h = small x sx
                j , larger = witness k
            in j , ≼-trans {b = L.suc (C.finite k)} (≼-suc h) larger

import B17Calibration as Original
btbo-requires : LEM → Rows.row 2 ≼ W.Y → SameTower
btbo-requires lem h = extract lem (≼-trans {a = L.suc C.omega-cut} {b = Rows.row 2} {c = W.Y} Original.finite-cut h)

VaryingTower : Set
VaryingTower = (k : ℕ) → Σ ℕ (Finite.Cofinal k)

extract-varying : LEM → C.omega-cut ≼ W.Y → VaryingTower
extract-varying lem lower k = Finite.necessary k lem (≼-trans {b = C.omega-cut}
  (≼l {f = C.finite} (suc (suc (suc k))) (Local.step (suc (suc k)))) lower)

collect-varying : VaryingTower → C.omega-cut ≼ W.Y
collect-varying pick = l≼ {f = C.finite} {b = W.Y} λ k → let n , co = pick k in
  ≼-trans {b = C.finite (suc (suc k))}
    (raise k (suc (suc k)) (N.m≤n⇒m≤1+n (N.m≤n⇒m≤1+n N.≤-refl)))
    (≼-trans {b = L.suc (C.finite (suc (suc k)))} (≼-suc (≼-refl _)) (Finite.sufficient k n co))

import B28FFinite as Fin
import B18CellState as State
base : ∀ n j → L.suc (C.finite 2) ≼ State.At.fresh (suc n) j
base n j = ≼-trans {a = L.suc (C.finite 2)} {b = L.suc (Fin.R.point 1)} {c = State.At.fresh (suc n) j}
  (s≼s {a = C.finite 2} {b = Fin.R.point 1} (OCF.Align.Value.≅→≼ {a = C.finite 2} {b = Fin.R.point 1}
    (L.≅-sym {a = Fin.R.point 1} {b = C.finite 2} (Fin.point 1))))
  (Fin.paid n j (Fin.R.at 1))

Hits : Set
Hits = ∀ k → Σ ℕ (λ n → Σ ℕ (λ j → L.suc (C.finite k) ≼ Cell.At.fresh n j))

hits : LEM → C.omega-cut ≼ W.Y → Hits
hits lem h k = let n , co = extract-varying lem h k in n , co (C.finite k) (≼-trans {b = C.finite (suc k)}
  (Local.step k) (raise (suc k) (suc (suc k)) (N.n≤1+n (suc k))))

from-hits : Hits → C.omega-cut ≼ W.Y
from-hits pay = l≼ {f = C.finite} {b = W.Y} λ k → let n , j , h = pay k in
  ≼-trans {b = L.suc (C.finite k)} (≼-suc (≼-refl _))
    (≼-trans {b = Cell.At.fresh n j} h (≼-trans {b = R.fresh (suc n)} (Cell.At.into n j)
      (Rows.into {x = R.fresh (suc n)} (suc n , R.lower (suc n)))))

import Survey.W4LegacyOmega as Old
import B25DOld as Chain

Prefixes : Set
Prefixes = ∀ i → Σ ℕ (λ n → Σ ℕ (λ j → L.suc (Old.p i) ≼ Cell.At.fresh n j))

old-to-feedback : LEM → Chain.point 2 ≼ W.Y → Prefixes
old-to-feedback lem h i = let n , j , p = hits lem (≼-trans {a = C.omega-cut} {b = Chain.point 2} {c = W.Y} (proj₁ Chain.point₂) h) (suc (suc i))
  in n , j , ≼-trans {b = L.suc (C.finite (suc (suc i)))} (s≼s (Old.upper i)) p

feedback-to-old : Prefixes → Chain.point 2 ≼ W.Y
feedback-to-old pay = ≼-trans {b = L.lim Old.p} (proj₁ Old.join) (l≼ each)
  where
  each : ∀ i → Old.p i ≼ W.Y
  each i = let n , j , h = pay i in ≼-trans {b = L.suc (Old.p i)} (≼-suc (≼-refl _)) (≼-trans {b = Cell.At.fresh n j} h
    (≼-trans {b = R.fresh (suc n)} (Cell.At.into n j) (Rows.into {x = R.fresh (suc n)} (suc n , R.lower (suc n)))))

second-prefix : ∀ n j → L.suc (Old.p 1) ≼ Cell.At.fresh (suc n) j
second-prefix n j = ≼-trans {b = L.suc (C.finite 2)} (s≼s OCF.Lean.YiXVTwo.pre1-upper) (base n j)
  where import OCF.Lean.YiXVTwo
```
