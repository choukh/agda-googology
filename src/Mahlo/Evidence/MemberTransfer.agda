{-# OPTIONS --safe --without-K #-}
module Mahlo.Evidence.MemberTransfer where

-- Critical-path experiment: pointwise maps suffice for transferring a fixed
-- distinguished predicate. No equality of types, codes, or proofs is needed.
-- Actual closure/code correspondence must still supply M/Pred maps below.
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import Mahlo.WellOrder.Locality as Locality
import Mahlo.WellOrder.Segments as Segments

module Transfer {a b m₀ p₀ m₁ p₁ : Level}
  (Valid : Nat → Set) (_<_ : Nat → Nat → Set)
  (A : Nat → Set a) (B : Nat → Set b)
  (M₀ : Nat → Set m₀) (Pred₀ : Nat → Nat → Set p₀)
  (M₁ : Nat → Set m₁) (Pred₁ : Nat → Nat → Set p₁)
  (a⇒b : (x : Nat) → A x → B x)
  (b⇒a : (x : Nat) → B x → A x)
  (m⇒ : (x : Nat) → M₀ x → M₁ x)
  (m⇐ : (x : Nat) → M₁ x → M₀ x)
  (p⇒ : (x y : Nat) → Pred₀ x y → Pred₁ x y)
  (p⇐ : (x y : Nat) → Pred₁ x y → Pred₀ x y) where

  module Forward = Locality.Compare M₀ Pred₀ M₁ Pred₁
  module Backward = Locality.Compare M₁ Pred₁ M₀ Pred₀
  module S = Segments.On Valid _<_

  w⇒ : (x : Nat) → Forward.Source.Generated x → Forward.Target.Generated x
  w⇒ x w = Forward.local-map (λ _ → ⊤)
    (λ y _ → m⇒ y) (λ y z _ → p⇐ y z) (λ _ _ _ _ → tt) x w tt

  w⇐ : (x : Nat) → Forward.Target.Generated x → Forward.Source.Generated x
  w⇐ x w = Backward.local-map (λ _ → ⊤)
    (λ y _ → m⇐ y) (λ y z _ → p⇒ y z) (λ _ _ _ _ → tt) x w tt

  forward : S.Segment A Forward.Source.Generated
    → S.Segment B Forward.Target.Generated
  S.Segment.valid (forward d) x bx = S.Segment.valid d x (b⇒a x bx)
  S.Segment.included (forward d) x bx =
    w⇒ x (S.Segment.included d x (b⇒a x bx))
  S.Segment.initial (forward d) x bx y wy lt =
    a⇒b y (S.Segment.initial d x (b⇒a x bx) y (w⇐ y wy) lt)

  backward : S.Segment B Forward.Target.Generated
    → S.Segment A Forward.Source.Generated
  S.Segment.valid (backward d) x ax = S.Segment.valid d x (a⇒b x ax)
  S.Segment.included (backward d) x ax =
    w⇐ x (S.Segment.included d x (a⇒b x ax))
  S.Segment.initial (backward d) x ax y wy lt =
    b⇒a y (S.Segment.initial d x (a⇒b x ax) y (w⇒ y wy) lt)
