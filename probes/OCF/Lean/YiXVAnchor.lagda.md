# YiXV：模拟推导中的字面起点
> 验收文件。`Anchor.Closed` 只记录模拟推导的零行是否取字面 `Ω₁`；不改变源树或证书。
> 编译定理：此证据对加法、next、第 0 层上折保持；实际 `ΩU`、`γ₁U` 已实填。
> 供自身层回灌时复用同一零行；不声称全链有此模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVAnchor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVPlus as P
import OCF.Lean.YiXVCarry as K
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

module Anchor (B : Base (suc zero)) where
  module A = S.Sim B
  module C = P.Closure B

  Closed : ∀ {x X} → A.U x X → Set
  Closed (A.uz {X = X} p q) = X ≡ O.Ω₁
  Closed (A.us h) = Closed h
  Closed (A.uw gd h q) = Closed h
  Closed (A.ul h) = ∀ n → Closed (h n)
  Closed (A.un h) = ∀ a y q → Closed (h a y q)
  Closed (A.uu gd h q) = Closed h

  plus-closed : ∀ {x X} (gdX : O.Gd X) (hx : A.U x X) → Closed hx →
    ∀ {y Y} (gdY : O.Gd Y) (hy : A.U y Y) → Closed hy → Closed (C.plus-comp gdX hx gdY hy)
  plus-closed gdX hx cx gdY (A.uz p q) cy = cx
  plus-closed gdX hx cx (O.gs gdY) (A.us hy) cy = plus-closed gdX hx cx gdY hy cy
  plus-closed gdX hx cx gdY (A.uw gdY₀ hy q) cy = plus-closed gdX hx cx gdY₀ hy cy
  plus-closed gdX hx cx gdY (A.ul h) cy = λ n → plus-closed gdX hx cx gdY (h n) (cy n)
  plus-closed gdX hx cx (O.gi law gb) (A.un h) cy = λ a y q → plus-closed gdX hx cx (gb y (O.s→1 q)) (h a y q) (cy a y q)
  plus-closed gdX hx cx gdY (A.uu gdY₀ hy q) cy = plus-closed gdX hx cx gdY₀ hy cy

  terms-closed : ∀ {x X} (gdX : O.Gd X) (hx : A.U x X) → Closed hx → (n : ℕ) → Closed (C.Power.terms gdX hx n)
  terms-closed gdX hx cx zero = cx
  terms-closed gdX hx cx (suc n) = plus-closed gdX hx cx (O.Gd-iter gdX (suc n)) (C.Power.terms gdX hx n) (terms-closed gdX hx cx n)

  next-closed : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) (gdX : O.Gd X) (hx : A.U x X) → Closed hx → Closed (C.next-comp nx gdX hx)
  next-closed nx gdX hx cx = terms-closed gdX hx cx

  upc-closed : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) (gdX : O.Gd X) (hx : A.U x (O.ψ₁ X)) → Closed hx →
    (σ : L.Simᴵ L.zero (L.suc L.zero)) (z : Tr zero) → Closed (K.Lift.upc-comp B nx gdX hx σ z)
  upc-closed nx gdX hx cx σ zero = cx
  upc-closed nx gdX hx cx σ (suc z) = next-closed (Upc-nz (suc zero) tt _ nx z)
    (O.Gd-ψ₁ (O.Gd-add⁰ gdX (read z))) (K.Lift.upc-comp B nx gdX hx σ z) (upc-closed nx gdX hx cx σ z)
  upc-closed nx gdX hx cx σ (lim f a) = λ n → upc-closed nx gdX hx cx σ (f n)
  upc-closed nx gdX hx cx σ (Ω () g)
  upc-closed nx gdX hx cx σ (up y () z e)

module A = Anchor I.D1

Ω-closed : A.Closed I.ΩU
Ω-closed a y q = refl

γ₁-closed : A.Closed K.γ₁U
γ₁-closed a y q = A.upc-closed (Ωt-nz (suc zero)) O.Gd-Ω K.ΩψU Ω-closed (λ r → L.suc r) (suc a)
```
