{-# OPTIONS --safe --without-K #-}
module Mahlo.WellOrder.Segments where

-- Setzer [Se98] Definition 4.12, using its explicitly stated equivalent form.
-- Valid and the order must later be instantiated with the reference notation.
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

module On (Valid : Nat → Set) (_<_ : Nat → Nat → Set) where
  record Segment {a b : Level} (A : Nat → Set a) (B : Nat → Set b)
    : Set (a ⊔ b) where
    field
      valid : (x : Nat) → A x → Valid x
      included : (x : Nat) → A x → B x
      initial : (x : Nat) → A x → (y : Nat) → B y → y < x → A y
  open Segment

  union : {i a b : Level} (I : Set i)
    (A : I → Nat → Set a) (B : Nat → Set b)
    → ((j : I) → Segment (A j) B)
    → Segment (λ x → Σ I (λ j → A j x)) B
  valid (union I A B segments) x (j , ax) = valid (segments j) x ax
  included (union I A B segments) x (j , ax) = included (segments j) x ax
  initial (union I A B segments) x (j , ax) y by lt =
    j , initial (segments j) x ax y by lt

  compose : {a b c : Level}
    {A : Nat → Set a} {B : Nat → Set b} {C : Nat → Set c}
    → Segment A B → Segment B C → Segment A C
  valid (compose ab bc) = valid ab
  included (compose ab bc) x ax = included bc x (included ab x ax)
  initial (compose ab bc) x ax y cy lt =
    initial ab x ax y (initial bc x (included ab x ax) y cy lt) lt
