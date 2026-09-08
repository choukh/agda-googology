{-# OPTIONS --safe --without-K #-}
module Mahlo.WellOrder.Locality where

-- Local transfer of positive generated predicates. This proves the
-- induction step of a locality argument, not the ordinal-specific locality
-- of M(A) or tau_A. Those must supply the displayed conversion maps.
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat)
import Mahlo.WellOrder.Accessible as Accessible

module Compare {m₀ p₀ m₁ p₁ : Level}
  (M₀ : Nat → Set m₀) (Pred₀ : Nat → Nat → Set p₀)
  (M₁ : Nat → Set m₁) (Pred₁ : Nat → Nat → Set p₁) where
  module Source = Accessible.Generate M₀ Pred₀
  module Target = Accessible.Generate M₁ Pred₁

  -- On K, target predecessors must be available to the source induction.
  -- The direction of edge-back is deliberately contravariant.
  local-map : {k : Level} (K : Nat → Set k)
    → ((x : Nat) → K x → M₀ x → M₁ x)
    → ((x y : Nat) → K x → Pred₁ x y → Pred₀ x y)
    → ((x y : Nat) → K x → Pred₁ x y → K y)
    → (x : Nat) → Source.Generated x → K x → Target.Generated x
  local-map K eligible-forward edge-back stays-inside =
    Source.least (λ x → K x → Target.Generated x)
      (λ x mx ih kx → Target.step (eligible-forward x kx mx)
        (λ y edge → ih y (edge-back x y kx edge) (stays-inside x y kx edge)))
