{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Fundamental.Mahlo where

-- Concrete entry points: no supplied validity predicate or comparison oracle.
-- Failure is explicit; total reference correctness is NOT yet certified.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.List using (List; []; _∷_)
open import Mahlo.Archive.Legacy.Notation.Syntax
import Mahlo.Archive.Legacy.Notation.Reference as R
import Mahlo.Archive.Legacy.Fundamental.FiniteSearch as FS

data Result (A : Set) : Set where
  ok : A → Result A
  invalid : Result A
  exhausted : Result A

scan : Term → Term → List Term → Result Term
scan bound best [] = ok best
scan bound best (x ∷ xs) with R.validOT x
... | nothing = exhausted
... | just false = scan bound best xs
... | just true with R.less x bound
...   | nothing = exhausted
...   | just false = scan bound best xs
...   | just true with R.less best x
...     | nothing = exhausted
...     | just true = scan bound x xs
...     | just false = scan bound best xs

-- Called only on a syntactic successor: remove its final φ_0(0).
predecessor : Term → Term
predecessor nil = nil
predecessor (cons p nil) = nil
predecessor (cons p (cons q qs)) = cons p (predecessor (cons q qs))

omega₁ : Term
omega₁ = single (omega one)

-- Only the countable part is an input to the internal sequence algorithm.
basicSequence : Term → Nat → Result Term
basicSequence a n with R.validOT a
... | nothing = exhausted
... | just false = invalid
... | just true with R.less a omega₁
...   | nothing = exhausted
...   | just false = invalid
...   | just true with equalZero a
  where
  equalZero : Term → Agda.Builtin.Bool.Bool
  equalZero nil = true
  equalZero _ = false
...     | true = ok nil
...     | false with isSuccessor a
...       | true = ok (predecessor a)
...       | false = scan a nil (FS.terms n)

ones : Nat → Term
ones zero = nil
ones (suc n) = cons (phi nil nil) (ones n)

-- Reference Ω_M is represented by M, not by the invalid raw omega M.
stageArgument : Nat → Term
stageArgument zero = single mahlo
stageArgument (suc n) = single (omega (cons mahlo (ones (suc n))))

stage : Nat → Term
stage n = single (psi omega₁ (stageArgument n))

endpointSequence : Nat → Result Term
endpointSequence n with R.validOT (stage n)
... | nothing = exhausted
... | just false = invalid
... | just true with R.less (stage n) omega₁
...   | nothing = exhausted
...   | just false = invalid
...   | just true = ok (stage n)
