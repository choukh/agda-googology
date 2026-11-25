# 首个单位具名上界可只查较低层询问

第四层，无条件。若第 a 个恢复值 Mₐ 盖住地址 (1,0) 在较低层实际询问的每一项，则该地址的完整单位严格低于 Mₐ₊₁。同一地址已兑现两个严格下界。反过来，完整单位有上界 Mₐ 时，所有这些询问都由同一个 Mₐ 盖住。[单位压缩](W4ReturnCap.lagda.md) · [已含标准塔的具体询问](W4ReturnCapLeaf.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCapNamed where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-suc; ≼-refl; ≅→≈ᵛ; l≼; s≼s)
import W4Block as W
import W4Ops as O
import WVOne as V
open V using (read; 𝟏)
import B8FreezeMain as Raw
import B12Strict as Strict
import B14Tower as TW
import B18TowerSlots as Slots
import B18TowerEmb as Emb
import B19PathShape as Shape
import B19IdealProduct as Law
import B20StandardInside as Std
import B21StandardShape as Rise
import B22MovingIndex as Fix
import B22TowerCut as Mon
import B27UEpsilon as Hull
import B27EpsilonCut as Cut
import B27Threshold as Row
import B28Orbit as Orbit
import B28OrbitValue as Names
import B31Address as Addr
import Survey.W4ReturnCap as C
import Survey.W4ReturnCapLeaf as Leaf
import Survey.W4ReturnRendezvous as Goal

open Law using (_∙_)
module A = C.Actual

join : ∀ (p q : O.Tr⁺ W.zero) → read (proj₁ (p O.⊞ q)) ≈ᵛ (read (proj₁ p) L.+ read (proj₁ q))
join p q = ((Raw.read-+′ (proj₁ p) v) , (V.read-+ (proj₁ p) v)) ∙
  Law.add (Law.id (read (proj₁ p))) (≅→≈ᵛ (Shape.read-shape (Rise.copy (proj₁ q))))
  where v = O.ι W.zero (proj₁ q)

raw = (O.Ωt W.zero O.⊞ Emb.standard 0) O.⊞ Emb.standard 1
slot : TW.At.slot A.r ≡ raw
slot = cong (λ b → b W.zero (W.ink W.self)) (Slots.At.all 1 W.zero)

raw-value : A.d ≈ᵛ ((𝟏 L.+ Std.std 0) L.+ Std.std 1)
raw-value = subst (λ b → read (proj₁ b) ≈ᵛ ((𝟏 L.+ Std.std 0) L.+ Std.std 1)) (sym slot)
  (join (O.Ωt W.zero O.⊞ Emb.standard 0) (Emb.standard 1) ∙
    Law.add (join (O.Ωt W.zero) (Emb.standard 0)) (Law.id (Std.std 1)))

Address = Σ ℕ (λ j → Addr.Addr (A.A.idx j))
ask : Address → V.T₀
ask (j , p) = Addr.readAt (A.A.idx j) (A.A.point j) p

Test : ℕ → Set
Test a = ∀ p → ask p ≼ Goal.M a

necessary : ∀ a → Goal.unit 1 0 ≼ Goal.M a → Test a
necessary a bound (j , p) = ≼-trans {b = A.parts (suc j)} (Addr.in-cost (A.A.idx j) (A.A.point j) p)
  (≼-trans {b = A.Q} (A.here (suc j)) (≼-trans {b = Goal.unit 1 0} C.lower bound))

old : ∀ a → L.suc (Goal.M a) ≼ Row.row (suc (suc a))
old zero = Row.below 2 (Orbit.target 0) (s≤s z≤n)
old (suc n) = Names.upper n

module Leaves (q : V.T₀) (bounds : ∀ p → ask p ≼ q) where
  module H = Hull.At q
  p : Std.std 1 ≼ q
  p = ≼-trans {b = ask (1 , proj₁ Leaf.witness)} (proj₂ Leaf.witness) (bounds (1 , proj₁ Leaf.witness))
  std-in : H.In (Std.std 1)
  std-in = H.down {x = Std.std 1} {y = q} p H.seed
  zero-in : H.In (Std.std 0)
  zero-in = H.down {x = Std.std 0} {y = Std.std 1}
    (≼-trans {b = L.suc (Std.std 0)} (≼-suc (≼-refl _)) (Rise.rise 0)) std-in
  one-in : H.In 𝟏
  one-in = H.down {x = 𝟏} {y = Std.std 0} (Strict.strict (proj₂ (Emb.standard 0))) zero-in
  d-in : H.In A.d
  d-in = H.down {x = A.d} {y = (𝟏 L.+ Std.std 0) L.+ Std.std 1} (proj₁ raw-value)
    (H.sumC {x = 𝟏 L.+ Std.std 0} {y = Std.std 1} (H.sumC {x = 𝟏} {y = Std.std 0} one-in zero-in) std-in)

  positive : 𝟏 ≼ q
  positive = ≼-trans {b = Std.std 1} (Strict.strict (proj₂ (Emb.standard 1))) p
  upper : Goal.unit 1 0 ≼ Fix.above q
  upper = subst (_≼ Fix.above q) C.same (A.Bound.upper q positive d-in
    (λ j → Addr.least (A.A.idx j) (A.A.point j) q (λ v → bounds (j , v))))

cost : V.T₀
cost = L.lim (λ j → A.parts (suc j))

upper : Goal.unit 1 0 ≼ Fix.above cost
upper = Leaves.upper cost λ { (j , p) → OCF.Align.Value.≼l {f = λ n → A.parts (suc n)} j
  (Addr.in-cost (A.A.idx j) (A.A.point j) p) }

lower : cost ≼ Goal.unit 1 0
lower = l≼ λ j → ≼-trans {b = A.Q} (A.here (suc j)) C.lower

closed : ∀ k → 2 ≤ k → ∀ x → L.suc x ≼ Row.row k → L.suc (Fix.above x) ≼ Row.row k
closed = Cut.At.closed

module Pay (a : ℕ) (bounds : Test a) where
  strict : L.suc (Goal.unit 1 0) ≼ Goal.M (suc a)
  strict = ≼-trans {a = L.suc (Goal.unit 1 0)} {b = L.suc (Fix.above (Goal.M a))} {c = Goal.M (suc a)}
    (s≼s (Leaves.upper (Goal.M a) bounds)) (≼-trans {b = Row.row (suc (suc a))}
      (closed (suc (suc a)) (s≤s (s≤s z≤n)) (Goal.M a) (old a)) (Names.lower a))

  bracket : Goal.Bracket 0
  bracket = Goal.bracket 1 0 (suc a) (Goal.seed 0 0)
    (≼-trans {b = L.suc (Goal.unit 1 0)} (≼-suc (≼-refl _)) strict)
```
