{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Universe.Predicates where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Universe.External using (Fam; module Close)

-- P_V(N) in the candidate V = Set interpretation.
SmallPred : Set₁
SmallPred = Nat → Set

module Coded (F : Fam → Fam) where
  open Close F

  -- P_F(N) is small even though P_V(N) is not.
  PredCode : Set
  PredCode = Nat → U

  decodePred : PredCode → SmallPred
  decodePred P x = El (P x)

  all : PredCode → U
  all P = pi nat P

  exists : PredCode → U
  exists P = sigma nat P

  indexedUnion : (i : U) → (El i → PredCode) → PredCode
  indexedUnion i P x = sigma i (λ j → P j x)

  all-decode : (P : PredCode) → El (all P) ≡ ((x : Nat) → decodePred P x)
  all-decode P = refl

  exists-decode : (P : PredCode) → El (exists P) ≡ Σ Nat (decodePred P)
  exists-decode P = refl

  union-decode : (i : U) (P : El i → PredCode) (x : Nat) →
    decodePred (indexedUnion i P) x ≡ Σ (El i) (λ j → decodePred (P j) x)
  union-decode i P x = refl
