# 三份 Ω₂ 的每一行只须检验第一次询问

第四层，无条件。给任意正则前缀追加一份 Ω₂ 后，下一行第一次询问已经包含前一整行。取两份作前缀，得到三份参照值和一列单次询问的双向值序。[原行分解](Reports-2026-11-19/attachments/B24RRows.agda.txt)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ThreeCopies where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≅→≼; l≼; ≼l; s≼s)
open import WVOne using (T₀; 𝟏)
open import WVTwo using (T₁)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B12Omega3Cuts as Sums
import B13Target as P
import B14RefFixed as F
import B19RowSecond as Coeff
import B23NFirst as Earlier
import B20StandardInside as Std
import B21StandardShape as Shape
import B22MovingIndex as E
import B22TowerCut as Cut
import B22RowSource as Tail
import B24RRows as Rows
import B24AQueries as Q

module First (p : A.Lev₂) (rp : p L.≅ p) where
  module Row = Rows.At p rp
  root = L.ψ⁰ (P.pass (p L.+ Ω₂ᴸ))
  first = λ n → Row.gain n 𝟏
  advance : T₁ → T₁
  advance t = F.collapse (Row.T t)
  seed = R.S.iter advance Ω₁ᴸ
  align : ∀ n → Row.y n L.≅ seed n
  align zero = L.Ω-refl _
  align (suc n) = F.pres (Row.from-live (align n))
  path : ∀ n → F.Select (seed n) (Row.kid (suc n) 𝟏)
  path zero = F.branch 0 F.here
  path (suc n) = F.map-select advance (λ _ → refl) (path n)
  prior : ∀ n → Row.node n ≼ first (suc n)
  prior n = ≼-trans {b = L.ψ⁰ (Row.T (seed n))}
    (≅→≼ (L.ψ⁰-≅ (Row.from-live (align n))))
    (F.value (F.map-select (λ t → L.ψ⁰ (Row.T t)) (λ _ → refl) (path n)))
  in-row : ∀ n → first n ≼ Row.node n
  in-row n = ≼-trans {b = L.lim (λ j → Row.iterate n (suc j))} (≼l 0 (≼-refl _))
    (≅→≼ (L.≅-sym (Row.shape n)))
  complete : root ≈ᵛ L.lim first
  complete = (l≼ λ n → ≼l (suc n) (prior n)) ,
    (l≼ λ n → ≼-trans {b = Row.node n} (in-row n) (R.at-below root n))

module Three = First (Y.ll 1) (Y.regular 1)
target = Q.recorded 2
test = Three.first

into-tower : ∀ m → (∀ n → test n ≼ Std.std m) → target ≼ Std.std m
into-tower m h = ≼-trans {b = L.lim test} (proj₁ Three.complete) (l≼ h)

from-tower : ∀ m → target ≼ Std.std m → ∀ n → test n ≼ Std.std m
from-tower m h n = ≼-trans {b = L.lim test} (≼l n (≼-refl _))
  (≼-trans {b = target} (proj₂ Three.complete) h)

benchmark : ∀ m → (∀ n → test n ≼ Std.std m) → L.suc (E.above target) ≼ Cut.cut
benchmark m h = Cut.inside {target} (≼l (suc m) (≼-trans {b = L.suc (Std.std m)}
  (s≼s (into-tower m h)) (Shape.rise m)))

two = Q.recorded 1
coefficient = P.pass (Y.ll 1)
parts = λ n → L.ψ⁰ (R.S.iter (coefficient L.+_) L.zero n)
first-shape : test 0 ≡ L.lim parts
first-shape = refl
first-copy : parts 1 ≡ two
first-copy = refl

two-in-first : L.suc (Q.recorded 1) ≼ test 0
two-in-first = Earlier.gain

module Copies = Sums.Sum coefficient (P.pass-pres (Y.regular 1))
parts-rise : ∀ n → L.suc (parts n) ≼ parts (suc n)
parts-rise n = ≼-trans {b = L.ψ⁰ (Copies.left n L.+ Coeff.p)}
  (Tail.Tail.one (Copies.left n) (Copies.reg n))
  (≼-trans {b = L.ψ⁰ (Copies.left n L.+ coefficient)} (Q.lead 1 (Copies.left n))
    (≅→≼ (L.ψ⁰-≅ (Copies.rotate n))))
```
