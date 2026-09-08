{-# OPTIONS --safe --without-K #-}
module Mahlo.Notation.Closure where

-- Finite closure on decomposition expressions, NOT yet Setzer's OT.
-- add denotes a supplied binary normal-form decomposition, not an ordinal
-- addition algorithm. Principal-sum normality and the actual order are pending.
-- The executable order test is an explicit parameter; no order law is assumed.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Mahlo.Universe.External using (Sum; inl; inr)
open import Mahlo.Notation.FiniteSupport

data Expr : Set where
  zero mahlo : Expr
  add phi psi : Expr → Expr → Expr
  omega : Expr → Expr

data ⊥ : Set where

True : Bool → Set
True true = ⊤
True false = ⊥

open On Expr public

guard : Bool → Family → Family
guard true xs = xs
guard false xs = []

guard-in : {A : Expr → Set} (b : Bool) {xs : Family}
  → True b → Holds A xs → Holds A (guard b xs)
guard-in true p q = q
guard-in false () q

guard-out : {A : Expr → Set} (b : Bool) (xs : Family)
  → Holds A (guard b xs) → Σ (True b) (λ _ → Holds A xs)
guard-out true xs p = tt , p
guard-out false xs ()

module Compute (lt : Expr → Expr → Bool) where
  -- A list of alternative finite supports, independent of the seed predicate.
  atom : Expr → Expr → Family
  atom a d = guard (lt d a) ((d ∷ []) ∷ [])

  K : Expr → Expr → Family
  K a zero = [] ∷ []
  K a mahlo = [] ∷ []
  K a (add b c) = tensor (K a b) (K a c) ++ atom a (add b c)
  K a (phi b c) = tensor (K a b) (K a c) ++ atom a (phi b c)
  K a (omega b) = K a b ++ atom a (omega b)
  K a (psi k c) = guard (lt a k) (tensor (K a k) (K a c)) ++ atom a (psi k c)

  -- This is a small predicate even if A is not decidable. K is computable;
  -- membership in the closure is not claimed decidable for arbitrary A.
  C : (Expr → Set) → Expr → Expr → Set
  C A a d = Holds A (K a d)

  atom-in : {A : Expr → Set} (a d : Expr)
    → A d → True (lt d a) → Holds A (atom a d)
  atom-in a d ad lt-da = guard-in (lt d a) lt-da (here (ad , tt))

  atom-out : {A : Expr → Set} (a d : Expr)
    → Holds A (atom a d) → Σ (A d) (λ _ → True (lt d a))
  atom-out a d p with guard-out (lt d a) ((d ∷ []) ∷ []) p
  ... | lt-da , here (ad , _) = ad , lt-da
  ... | _ , there ()

  seed : {A : Expr → Set} (a d : Expr) → A d → True (lt d a) → C A a d
  seed a zero ad p = here tt
  seed a mahlo ad p = here tt
  seed a (add b c) ad p = right (tensor (K a b) (K a c)) (atom-in a (add b c) ad p)
  seed a (phi b c) ad p = right (tensor (K a b) (K a c)) (atom-in a (phi b c) ad p)
  seed a (omega b) ad p = right (K a b) (atom-in a (omega b) ad p)
  seed a (psi k c) ad p = right (guard (lt a k) (tensor (K a k) (K a c)))
    (atom-in a (psi k c) ad p)

  -- Independent inductive rule specification. The two translations below
  -- certify both soundness and completeness of the finite support algorithm.
  data Derivable (A : Expr → Set) (a : Expr) : Expr → Set where
    from-seed : {d : Expr} → A d → True (lt d a) → Derivable A a d
    base-zero : Derivable A a zero
    base-mahlo : Derivable A a mahlo
    by-add : {b c : Expr} → Derivable A a b → Derivable A a c → Derivable A a (add b c)
    by-phi : {b c : Expr} → Derivable A a b → Derivable A a c → Derivable A a (phi b c)
    by-omega : {b : Expr} → Derivable A a b → Derivable A a (omega b)
    by-psi : {k c : Expr} → True (lt a k)
      → Derivable A a k → Derivable A a c → Derivable A a (psi k c)

  complete : {A : Expr → Set} {a d : Expr} → Derivable A a d → C A a d
  complete {a = a} (from-seed {d} ad p) = seed a d ad p
  complete base-zero = here tt
  complete base-mahlo = here tt
  complete (by-add p q) = left (tensor-in (complete p) (complete q))
  complete (by-phi p q) = left (tensor-in (complete p) (complete q))
  complete (by-omega p) = left (complete p)
  complete {a = a} (by-psi {k} lt-ak p q) =
    left (guard-in (lt a k) lt-ak (tensor-in (complete p) (complete q)))

  sound : {A : Expr → Set} (a d : Expr) → C A a d → Derivable A a d
  sound a zero p = base-zero
  sound a mahlo p = base-mahlo
  sound a (add b c) p with split (tensor (K a b) (K a c)) (atom a (add b c)) p
  ... | inl q with tensor-out (K a b) (K a c) q
  ...   | r , s = by-add (sound a b r) (sound a c s)
  sound a (add b c) p | inr q with atom-out a (add b c) q
  ... | ad , lt-da = from-seed ad lt-da
  sound a (phi b c) p with split (tensor (K a b) (K a c)) (atom a (phi b c)) p
  ... | inl q with tensor-out (K a b) (K a c) q
  ...   | r , s = by-phi (sound a b r) (sound a c s)
  sound a (phi b c) p | inr q with atom-out a (phi b c) q
  ... | ad , lt-da = from-seed ad lt-da
  sound a (omega b) p with split (K a b) (atom a (omega b)) p
  ... | inl q = by-omega (sound a b q)
  ... | inr q with atom-out a (omega b) q
  ...   | ad , lt-da = from-seed ad lt-da
  sound a (psi k c) p with split (guard (lt a k) (tensor (K a k) (K a c))) (atom a (psi k c)) p
  ... | inl q with guard-out (lt a k) (tensor (K a k) (K a c)) q
  ...   | lt-ak , r with tensor-out (K a k) (K a c) r
  ...     | s , t = by-psi lt-ak (sound a k s) (sound a c t)
  sound a (psi k c) p | inr q with atom-out a (psi k c) q
  ... | ad , lt-da = from-seed ad lt-da

  monotone-C : {A B : Expr → Set} → ((d : Expr) → A d → B d)
    → (a d : Expr) → C A a d → C B a d
  monotone-C f a d = monotone f

  finite-character : {A : Expr → Set} (a d : Expr) → C A a d
    → Σ (List Expr) (λ xs → Σ (All A xs) (λ _ → C (λ x → x ∈ xs) a d))
  finite-character a d = finite-witness

  decide-C : {A : Expr → Set} → ((d : Expr) → Dec (A d))
    → (a d : Expr) → Dec (C A a d)
  decide-C dec a d = decide dec (K a d)

  -- Locality at the SAME cutoff; no cross-cutoff/order theorem is claimed.
  local : {A B : Expr → Set} (a : Expr)
    → ((d : Expr) → True (lt d a) → A d → B d)
    → {d : Expr} → Derivable A a d → Derivable B a d
  local a f (from-seed {d} ad p) = from-seed (f d p ad) p
  local a f base-zero = base-zero
  local a f base-mahlo = base-mahlo
  local a f (by-add p q) = by-add (local a f p) (local a f q)
  local a f (by-phi p q) = by-phi (local a f p) (local a f q)
  local a f (by-omega p) = by-omega (local a f p)
  local a f (by-psi r p q) = by-psi r (local a f p) (local a f q)

  local-C : {A B : Expr → Set} (a : Expr)
    → ((d : Expr) → True (lt d a) → A d → B d)
    → (d : Expr) → C A a d → C B a d
  local-C a f d p = complete (local a f (sound a d p))

  -- Candidate predicates on expressions. Validity is still supplied; proving
  -- that this is the reference C on valid normal forms is a separate task.
  module Predicates (Valid : Expr → Set) (A : Expr → Set) where
    M : Expr → Set
    M d = Σ (Valid d) (λ _ → C A d d)

    Tau : Expr → Expr → Set
    Tau a d = Σ (Valid d) (λ _ → Σ (C A a d) (λ _ → True (lt d a)))

    seed-Tau : (a d : Expr) → Valid d → A d → True (lt d a) → Tau a d
    seed-Tau a d vd ad p = vd , seed a d ad p , p
