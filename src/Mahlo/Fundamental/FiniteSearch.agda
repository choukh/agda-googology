{-# OPTIONS --safe --without-K #-}
module Mahlo.Fundamental.FiniteSearch where

-- Definition-first candidate: finite-height search fundamental sequences.
-- Actual OT validity and order decisions are not yet implemented here.
-- No claim of Bachmann properties or reference FGH calibration is made.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Mahlo.Notation.Syntax using (Term; Principal; nil; cons; phi; psi; omega; mahlo)
open import Mahlo.Notation.FiniteSupport using (_++_)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

pairs : {A B D : Set} → (A → B → D) → List A → List B → List D
pairs f [] ys = []
pairs f (x ∷ xs) ys = map (f x) ys ++ pairs f xs ys

max : Nat → Nat → Nat
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

mutual
  height : Term → Nat
  height nil = zero
  height (cons p ps) = suc (max (heightP p) (height ps))

  heightP : Principal → Nat
  heightP mahlo = zero
  heightP (phi a b) = suc (max (height a) (height b))
  heightP (psi a b) = suc (max (height a) (height b))
  heightP (omega a) = suc (height a)

-- Enumerate ambient syntax, then filter by OT (not merely T').
-- These lists are finite but can be very large; this is not optimized.
mutual
  terms : Nat → List Term
  terms zero = nil ∷ []
  terms (suc n) = nil ∷ pairs cons (principals n) (terms n)

  principals : Nat → List Principal
  principals zero = mahlo ∷ []
  principals (suc n) = mahlo ∷
    (pairs phi (terms n) (terms n) ++
     pairs psi (terms n) (terms n) ++ map omega (terms n))

module Search (validOT : Term → Bool) (less : Term → Term → Bool) where
  choose : Term → Term → Term → Term
  choose bound best candidate with validOT candidate
  ... | false = best
  ... | true with less candidate bound
  ...   | false = best
  ...   | true with less best candidate
  ...     | true = candidate
  ...     | false = best

  scan : Term → Term → List Term → Term
  scan bound best [] = best
  scan bound best (candidate ∷ rest) = scan bound (choose bound best candidate) rest

  -- Intended for nonzero countable limits only. For arbitrary Boolean
  -- arguments this is just a finite computation, not a certified sequence.
  limit-sequence : Term → Nat → Term
  limit-sequence bound n = scan bound nil (terms n)
