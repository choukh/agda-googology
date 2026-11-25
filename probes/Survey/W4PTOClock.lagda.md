# 在固定的实际塔中收集变长反馈

第四层，无条件。以零层树作迭代次数，对第 25 批的对角运算按次数归纳。保留同一个二层前缀，后继只在一级系数上多作一次右加。
用于比较 $ID_2$ 深度 3 的首个询问。记 $W$ 为从已兑现的两份前缀的第零支开始，作全部有限次对角迭代的值上确界。[塔项与询问](W4PTOGamma.lagda.md) · [原对角运算](Reports-2026-11-19/attachments/B25ARank.agda.txt)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4PTOClock where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; s≼s; l≼; ≼l; ≅→≼; z≼)
open import WVOne using (T₀; 𝟏; read)
open import WVTwo using (T₁)
open import B12LimitSrc using (Lev₂)
import B12Omega3Ref as R
import B15RefMonotone as M
import B15RefAlgebra as Algebra
import B16RefFive as F
import B20OldTail as Tail
import B20OldSource as Strict
import B20OldRanks as Rank
import B20RowIndex as Index
import B20StandardInside as Std
import B21CrossCut as Cut
import B21CrossCoefficient as Coef
import B21CrossScalar as Scalar
import B21TowerGrowth as Tower
import B22MovingIndex as Eps
import B24ROrbit as Seed
import B24RExit as Entry
import B25ARank as X
import B25ADiagonal as Diag
import B25ACap as Cap
import B25AOrbit as Orbit
import B27UEpsilon as Inside

run : (x : T₀) → T₀ → T₀
run x L.zero = x
run x (L.suc t) = X.diagonal (run x t)
run x (L.lim f) = L.lim (λ n → run x (f n))

stamp : T₀ → T₀
stamp t = L.ωᶜ L.+ t

letter : T₀ → T₁
letter t = F.g (stamp t)

regular : ∀ t → letter t L.≅ letter t
regular t = F.regular (L.≅-refl⁰ (stamp t))

coeff-reg : Coef.coeff L.≅ Coef.coeff
coeff-reg = L.l≅ λ n → L.≅-trans (L.≅-sym (Coef.match n)) (Coef.match n)

fits : ∀ t → M.Below Coef.coeff (letter t)
fits L.zero = Cut.coef
fits (L.suc t) = M.right 1 (fits t)
fits (L.lim f) = M.right 0 (fits (f 0))

module Prefix (p : Lev₂) (rp : p L.≅ p) where
  module V = Scalar.At p
  q = λ t → V.add (letter t)
  rq : ∀ t → q t L.≅ q t
  rq t = L.add-≅ {σ = L.suc} {σ′ = L.suc} rp (regular t)

  plus : ∀ t → (q t L.+ L.up L.zero Coef.coeff) L.≅ V.add (letter t L.+ Coef.coeff)
  plus t = L.≅-trans (R.assoc {A = p} {B = L.up L.zero (letter t)} {C = q t}
    L.suc L.suc (rq t) coeff-reg)
    (L.add-≅ {σ = R.idσ} {σ′ = L.suc} rp
      (L.add-≅ {σ = L.suc} {σ′ = λ j → j} (L.upˡ (regular t)) coeff-reg))

  tick : ∀ t x → x ≼ V.f (letter t) → X.diagonal x ≼ V.f (letter (L.suc t))
  tick t x h = ≼-trans {b = L.lim (λ n → L.ψ⁰ (Rank.threshold n (q t)))}
    (X.all x (q t) (rq t) h)
    (≼-trans {b = V.f (letter t L.+ Coef.coeff)}
      (≅→≼ (L.ψ⁰-≅ (L.≅-trans (Coef.same (rq t)) (plus t))))
      (proj₁ (V.both (M.right 2 (M.plus (M.e₀ M.ω₁ (≼-refl (stamp t))) (fits t))))))

  start : L.ψ⁰ p ≼ V.f (letter L.zero)
  start = ≼-trans {b = L.suc (L.ψ⁰ p)} (≼-suc (≼-refl _))
    (≼-trans {b = L.ψ⁰ (Tail.next p)} (Strict.Actual.strict-step p)
      (proj₁ (V.both (M.root M.ω₁ L.ωᶜ))))

  follows : ∀ x → x ≼ L.ψ⁰ p → ∀ t → run x t ≼ V.f (letter t)
  follows x h L.zero = ≼-trans {b = L.ψ⁰ p} h start
  follows x h (L.suc t) = tick t (run x t) (follows x h t)
  follows x h (L.lim f) = l≼ (λ n → ≼l n (follows x h (f n)))

  collect : ∀ x → x ≼ L.ψ⁰ p → ∀ t → stamp t ≼ V.track F.g 1 →
    run x t ≼ L.ψ⁰ (Tower.add p)
  collect x h t clock = ≼-trans {b = V.f (letter t)} (follows x h t)
    (≼-trans {b = V.f (F.g (V.track F.g 1))} (proj₁ (V.both (M.e₀ M.ω₁ clock)))
      (≼-trans {b = V.f (Algebra.E WSLevel.Ω₁ᴸ WSLevel.Ω₁ᴸ)} (≼l 1 (≼-refl _))
        (≼-trans (≼l 0 (≼l 0 (≼l 1 (≼l 0 (≼-refl _)))))
          (≅→≼ (L.ψ⁰-≅ (L.add-≅ {σ = L.suc} {σ′ = L.suc} rp (L.≅-sym Index.collapse)))))))
    where import WSLevel
```

同一座塔容纳的时钟包括起点值 $x$ 自身，以及 $x$ 上方第一个 ε 点的整个严格初段（以有限轮 ω 幂的证据给出）。在 $x=D$ 时，仅取 $\omega+1$ 就足以严格超过 $W$。

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym)
open import OCF.Align.Value using (≼lim⁻)
import B18Product as Product
import B19IdealArithmetic as Ar
import B22TowerCut as Towers
import W4Fold

module Clocks (p : Lev₂) (rp : p L.≅ p) where
  module H = Inside.At (L.ψ⁰ p)
  module P = Prefix p rp
  one : H.In 𝟏
  one = H.sucC {L.zero} (H.down {L.zero} {L.ψ⁰ p} z≼ H.seed)
  omega : H.In L.ωᶜ
  omega = H.down {L.ωᶜ} {Ar.norm 𝟏} (Product.one-left L.ωᶜ) (H.expC {𝟏} one)
  room : ∀ t → H.In t → stamp t ≼ P.V.track F.g 1
  room t b = ≼-trans {b = L.suc (stamp t)} (≼-suc (≼-refl _))
    (≼-trans {b = Eps.above (L.ψ⁰ p)} (H.finite {stamp t} (H.sumC {L.ωᶜ} {t} omega b))
      (≼-trans {b = L.ψ⁰ (Tail.next p)} (Cap.Start.upper p rp)
        (≼-trans {b = L.ψ⁰ (Tail.block p)} (≼l 1 (≼-refl _)) (≅→≼ (Diag.Ref.k1 p rp)))))
  small : ∀ t → L.suc t ≼ Eps.above (L.ψ⁰ p) → H.In t
  small t h with ≼lim⁻ {a = t} {f = Eps.steps (L.ψ⁰ p)} h
  ... | n Data.Product., e = n Data.Product., e
  fixed : ∀ m → L.ψ⁰ p ≼ Std.std (Tower.At.k m) → ∀ x → x ≼ L.ψ⁰ p →
    ∀ t → H.In t → run x t ≼ Std.std (Tower.At.top m)
  fixed m d x h t b = ≼-trans {b = L.ψ⁰ (Tower.add p)} (P.collect x h t (room t b))
    (Tower.At.Standard.coefficient m p rp d)

module Actual = Clocks X.p X.rp

start-in-two : L.ψ⁰ X.p ≼ Std.std 2
start-in-two = ≼-trans {b = Seed.D} (≅→≼ (L.≅-sym Entry.input)) (Orbit.point 0)

in-four : ∀ t → Actual.H.In t → run Seed.D t ≼ Std.std 4
in-four = Actual.fixed 0 start-in-two Seed.D (≅→≼ Entry.input)

old-finite : ∀ n → Orbit.seq n ≡ run Seed.D (L.natᶜ n)
old-finite zero = refl
old-finite (suc n) = cong X.diagonal (old-finite n)

whole-clock : Orbit.whole ≼ run Seed.D L.ωᶜ
whole-clock = l≼ λ n → ≼l {f = λ k → run Seed.D (L.natᶜ k)} n
  (subst (Orbit.seq n ≼_) (old-finite n) (≼-refl _))

strict-in-four : L.suc Orbit.whole ≼ Std.std 4
strict-in-four = ≼-trans {b = L.suc (run Seed.D L.ωᶜ)} (s≼s whole-clock)
  (≼-trans {b = run Seed.D (L.suc L.ωᶜ)} (Orbit.strict-step (run Seed.D L.ωᶜ))
    (in-four (L.suc L.ωᶜ) (Actual.H.sucC {L.ωᶜ} Actual.omega)))

self-in-four : run Seed.D Seed.D ≼ Std.std 4
self-in-four = in-four Seed.D (Actual.H.down {Seed.D} {L.ψ⁰ X.p} (≅→≼ Entry.input) Actual.H.seed)

terminal : L.suc Orbit.whole ≼ read W4Fold.EBOᶜ
terminal = ≼-trans {b = Std.std 4} strict-in-four
  (≼-trans {b = Towers.cut} (≼l {f = Std.std} 4 (≼-refl _)) Towers.terminal)
```
