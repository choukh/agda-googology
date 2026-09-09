{-# OPTIONS --safe --without-K #-}
module Mahlo.Growth.Target where

-- Definition-first checkpoint. The evaluator is implemented; the Mahlo
-- notation, fundamental sequences and uniform certificates are still inputs.
-- No inhabitant of MahloInput is claimed to represent the reference ordinal.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)

data Empty : Set where

iterate : (Nat → Nat) → Nat → Nat → Nat
iterate f zero n = n
iterate f (suc k) n = f (iterate f k n)

module Hierarchy (Ord : Set) where
  data View : Set where
    zeroV : View
    successorV : Ord → View
    limitV : (Nat → Ord) → View

  Branch : View → Set
  Branch zeroV = Empty
  Branch (successorV a) = ⊤
  Branch (limitV seq) = Nat

  child : (v : View) → Branch v → Ord
  child zeroV ()
  child (successorV a) _ = a
  child (limitV seq) n = seq n

  module WithView (view : Ord → View) where
    -- Accessibility of the specified descent, not automatically of the
    -- whole reference ordering. Its connection to that ordering is a debt.
    data Accessible (a : Ord) : Set where
      access : ((b : Branch (view a)) → Accessible (child (view a) b))
        → Accessible a

    fold : (P : Ord → Set)
      → ((a : Ord) → ((b : Branch (view a)) → P (child (view a) b)) → P a)
      → (a : Ord) → Accessible a → P a
    fold P step a (access below) =
      step a (λ b → fold P step (child (view a) b) (below b))

    equation : (v : View) → (Branch v → Nat → Nat) → Nat → Nat
    equation zeroV below n = suc n
    equation (successorV a) below n = iterate (below tt) (suc n) n
    equation (limitV seq) below n = below n n

    F : (a : Ord) → Accessible a → Nat → Nat
    F = fold (λ _ → Nat → Nat) (λ a → equation (view a))

-- This record contains computational inputs only. It is deliberately NOT a
-- certificate of Mahlo strength: even much weaker systems can inhabit it.
-- Reference correctness is specified separately in DEFINITION-FIRST.md.
record MahloInput : Set₁ where
  field
    Ord : Set
  module H = Hierarchy Ord
  field
    view : Ord → H.View
  module Eval = H.WithView view
  field
    stage : Nat → Ord
    stage-accessible : (n : Nat) → Eval.Accessible (stage n)

module Target (input : MahloInput) where
  open MahloInput input

  -- Intended stage n = ψ_{Ω₁}(Ω_{M+n}), using the reference normalization.
  -- The endpoint convention is Top[n] = stage n, with no input shift.
  FαM : Nat → Nat
  FαM n = Eval.F (stage n) (stage-accessible n) n

  -- Freeze k only after selecting the concrete numerical target.
  N_M : Nat → Nat
  N_M k = FαM k
