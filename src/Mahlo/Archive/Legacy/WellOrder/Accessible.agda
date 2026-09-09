{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.WellOrder.Accessible where

-- Positive inductive generation for the rule in Setzer [Se98],
-- Assumption 4.10. M and predecessor membership remain explicit parameters;
-- their ordinal-specific definitions and locality laws are not supplied here.
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

module Generate {m p : Level}
  (M : Nat → Set m) (Pred : Nat → Nat → Set p) where

  data Generated (x : Nat) : Set (m ⊔ p) where
    step : M x → ((y : Nat) → Pred x y → Generated y) → Generated x

  eligible : {x : Nat} → Generated x → M x
  eligible (step mx below) = mx

  predecessor : {x y : Nat} → Generated x → Pred x y → Generated y
  predecessor (step mx below) edge = below _ edge

  -- Proof-relevant dependent elimination, with unrestricted target level.
  induction : {q : Level} (Q : (x : Nat) → Generated x → Set q)
    → ((x : Nat) (mx : M x) (below : (y : Nat) → Pred x y → Generated y)
        → ((y : Nat) (edge : Pred x y) → Q y (below y edge))
        → Q x (step mx below))
    → (x : Nat) (w : Generated x) → Q x w
  induction Q advance x (step mx below) =
    advance x mx below (λ y edge → induction Q advance y (below y edge))

  -- Leastness: every class closed under the rule contains Generated.
  least : {q : Level} (Q : Nat → Set q)
    → ((x : Nat) → M x → ((y : Nat) → Pred x y → Q y) → Q x)
    → (x : Nat) → Generated x → Q x
  least Q closed = induction (λ x _ → Q x)
    (λ x mx below ih → closed x mx ih)

  -- The premise may also use membership in Generated, as in [Se98] 4.10(b).
  induct : {q : Level} (Q : Nat → Set q)
    → ((x : Nat) → Generated x → M x
        → ((y : Nat) → Pred x y → Q y) → Q x)
    → (x : Nat) → Generated x → Q x
  induct Q closed = induction (λ x _ → Q x)
    (λ x mx below ih → closed x (step mx below) mx ih)

  -- Rule membership is equivalent to eligibility plus generated predecessors.
  unfold : (x : Nat) → Generated x →
    Σ (M x) (λ _ → (y : Nat) → Pred x y → Generated y)
  unfold x (step mx below) = mx , below

  fold : (x : Nat) →
    Σ (M x) (λ _ → (y : Nat) → Pred x y → Generated y) → Generated x
  fold x (mx , below) = step mx below
