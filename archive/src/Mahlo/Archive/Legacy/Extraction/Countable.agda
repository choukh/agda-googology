{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Extraction.Countable where

-- E0: extract branching from a tiny universe of arities.
-- No ordinal notation, comparison, or supplied fundamental sequence.
-- This preserves tree descent; it does NOT classify ordinal limits.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Mahlo.Archive.Legacy.Universe.External as External

data Empty : Set where

data Code : Set where
  empty unit natural : Code

El : Code → Set
El empty = Empty
El unit = ⊤
El natural = Nat

data Tree : Set where
  node : (a : Code) → (El a → Tree) → Tree

data BranchTree : Set where
  leaf : BranchTree
  next : BranchTree → BranchTree
  sup : (Nat → BranchTree) → BranchTree

extract : Tree → BranchTree
extract (node empty f) = leaf
extract (node unit f) = next (extract (f tt))
extract (node natural f) = sup (λ n → extract (f n))

data Child : Tree → Tree → Set where
  branch : {a : Code} {f : El a → Tree} (x : El a) → Child (f x) (node a f)

data Below : BranchTree → BranchTree → Set where
  next-child : {t : BranchTree} → Below t (next t)
  sup-child : {f : Nat → BranchTree} (n : Nat) → Below (f n) (sup f)

preserves-child : {s t : Tree} → Child s t → Below (extract s) (extract t)
preserves-child (branch {a = empty} ())
preserves-child (branch {a = unit} tt) = next-child
preserves-child (branch {a = natural} n) = sup-child n

data Accessible (t : BranchTree) : Set where
  access : (∀ {s} → Below s t → Accessible s) → Accessible t

all-accessible : (t : BranchTree) → Accessible t
all-accessible leaf = access (λ ())
all-accessible (next t) = access (λ { next-child → all-accessible t })
all-accessible (sup f) = access (λ { (sup-child n) → all-accessible (f n) })

finite : Nat → Tree
finite zero = node empty (λ ())
finite (suc n) = node unit (λ _ → finite n)

finite-output : Nat → BranchTree
finite-output zero = leaf
finite-output (suc n) = next (finite-output n)

finite-correct : (n : Nat) → extract (finite n) ≡ finite-output n
finite-correct zero = refl
finite-correct (suc n) rewrite finite-correct n = refl

omega-input : Tree
omega-input = node natural finite

-- Every extracted branch is the corresponding finite tree, uniformly in n.
omega-branch : (n : Nat) → extract (finite n) ≡ finite-output n
omega-branch = finite-correct

-- Obstruction to extending El-enumeration to arbitrary pi codes.
-- This is a constructive diagonal argument; no excluded middle or funext.
not : Bool → Bool
not true = false
not false = true

no-fixed-point : (b : Bool) → not b ≡ b → Empty
no-fixed-point true ()
no-fixed-point false ()

at : {f g : Nat → Bool} → f ≡ g → (n : Nat) → f n ≡ g n
at refl n = refl

Surjective : (Nat → (Nat → Bool)) → Set
Surjective e = (f : Nat → Bool) → Σ Nat (λ n → f ≡ e n)

no-enumeration : (e : Nat → (Nat → Bool)) → Surjective e → Empty
no-enumeration e covers with covers (λ n → not (e n n))
... | n , eq = no-fixed-point (e n n) (at eq n)

-- The same obstruction inside the actual external universe, for every F.
module InExternal (F : External.Fam → External.Fam) where
  module U = External.Close F

  bit-functions : U.U
  bit-functions = U.pi U.nat (λ _ → U.fin 2)

  flip : External.Fin 2 → External.Fin 2
  flip External.fzero = External.fsuc External.fzero
  flip (External.fsuc External.fzero) = External.fzero

  flip-not-fixed : (b : External.Fin 2) → flip b ≡ b → Empty
  flip-not-fixed External.fzero ()
  flip-not-fixed (External.fsuc External.fzero) ()

  at-bit : {f g : U.El bit-functions} → f ≡ g → (n : Nat) → f n ≡ g n
  at-bit refl n = refl

  no-decoded-enumeration : (e : Nat → U.El bit-functions)
    → ((f : U.El bit-functions) → Σ Nat (λ n → f ≡ e n)) → Empty
  no-decoded-enumeration e covers with covers (λ n → flip (e n n))
  ... | n , eq = flip-not-fixed (e n n) (at-bit eq n)
