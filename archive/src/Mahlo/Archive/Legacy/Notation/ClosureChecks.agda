{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Notation.ClosureChecks where

-- Branch regressions for the computation engine, not ordinal comparisons.
-- The artificial Boolean table below deliberately has no OT interpretation.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Notation.FiniteSupport using (Any; here; there; All; _∈_; first)
open import Mahlo.Archive.Legacy.Notation.Closure

blocked : Expr → Expr → Bool
blocked _ _ = false

module B = Compute blocked

blocked-psi-has-no-support : B.K zero (psi mahlo zero) ≡ []
blocked-psi-has-no-support = refl

blocked-psi-not-derivable : {A : Expr → Set} → B.Derivable A zero (psi mahlo zero) → ⊥
blocked-psi-not-derivable p with B.complete p
... | ()

-- Ordinary constructors can be built without any seeds, even when all
-- comparisons are false. The singleton empty support differs from no support.
closed-expression : B.K zero (phi (omega mahlo) (add zero mahlo)) ≡ ([] ∷ [])
closed-expression = refl

cut atom : Expr
cut = omega zero
atom = psi mahlo zero

table : Expr → Expr → Bool
table (psi mahlo zero) (omega zero) = true
table _ _ = false

module S = Compute table

-- The psi construction is blocked (cut < mahlo is false), but it may be
-- supplied as a seed below cut. Repetition in a finite support is harmless.
seed-only : S.K cut atom ≡ ((atom ∷ []) ∷ [])
seed-only = refl

paired-seeds : S.K cut (add atom atom) ≡ ((atom ∷ atom ∷ []) ∷ [])
paired-seeds = refl

paired-certificate : S.C (λ x → x ∈ (atom ∷ [])) cut (add atom atom)
paired-certificate = here (first , first , tt)
  where open import Agda.Builtin.Sigma using (_,_)

enabled : Expr → Expr → Bool
enabled zero mahlo = true
enabled _ _ = false

module E = Compute enabled

-- With the guard enabled, both constructor arguments supply empty supports.
enabled-psi : E.K zero (psi mahlo zero) ≡ ([] ∷ [])
enabled-psi = refl
