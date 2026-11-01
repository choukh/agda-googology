{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Notation.SyntaxBridge where

-- A faithful representation of principal sequences in the existing closure
-- expressions. This is a syntactic bridge, not yet an OT/closure theorem.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (tt)
open import Mahlo.Archive.Legacy.Notation.FiniteSupport using (All; _∈_; first; later)
open import Mahlo.Archive.Legacy.Notation.Syntax
import Mahlo.Archive.Legacy.Notation.Closure as C

cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : {A B D : Set} (f : A → B → D) {a a′ : A} {b b′ : B}
  → a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
cong₂ f refl refl = refl

mutual
  encode : Term → C.Expr
  encode nil = C.zero
  encode (cons p nil) = encodeP p
  encode (cons p (cons q ps)) = C.add (encodeP p) (encode (cons q ps))

  encodeP : Principal → C.Expr
  encodeP (phi a b) = C.phi (encode a) (encode b)
  encodeP (psi k b) = C.psi (encode k) (encode b)
  encodeP (omega a) = C.omega (encode a)
  encodeP mahlo = C.mahlo

-- This total function also flattens noncanonical expressions. It does not
-- sort, evaluate ordinal addition, or certify raw/normal-form validity.
flatten : C.Expr → Term
flatten C.zero = nil
flatten C.mahlo = single mahlo
flatten (C.add a b) = append (flatten a) (flatten b)
flatten (C.phi a b) = single (phi (flatten a) (flatten b))
flatten (C.psi k b) = single (psi (flatten k) (flatten b))
flatten (C.omega a) = single (omega (flatten a))

mutual
  roundtrip : (a : Term) → flatten (encode a) ≡ a
  roundtrip nil = refl
  roundtrip (cons p nil) = roundtripP p
  roundtrip (cons p (cons q ps)) = cong₂ append (roundtripP p) (roundtrip (cons q ps))

  roundtripP : (p : Principal) → flatten (encodeP p) ≡ single p
  roundtripP (phi a b) = cong₂ (λ x y → single (phi x y)) (roundtrip a) (roundtrip b)
  roundtripP (psi k b) = cong₂ (λ x y → single (psi x y)) (roundtrip k) (roundtrip b)
  roundtripP (omega a) = cong (λ x → single (omega x)) (roundtrip a)
  roundtripP mahlo = refl

injective : {a b : Term} → encode a ≡ encode b → a ≡ b
injective {a} {b} eq with cong flatten eq
... | flat-eq rewrite roundtrip a | roundtrip b = flat-eq

canonicalize : C.Expr → C.Expr
canonicalize e = encode (flatten e)

idempotent : (e : C.Expr) → canonicalize (canonicalize e) ≡ canonicalize e
idempotent e rewrite roundtrip (flatten e) = refl

-- The inverse direction holds precisely on this chosen representation.
Canonical : C.Expr → Set
Canonical e = canonicalize e ≡ e

encoded-canonical : (a : Term) → Canonical (encode a)
encoded-canonical a = cong encode (roundtrip a)

flatten-list : List C.Expr → List Term
flatten-list [] = []
flatten-list (e ∷ es) = flatten e ∷ flatten-list es

flatten-all : {A : Term → Set} (es : List C.Expr)
  → All (λ e → A (flatten e)) es → All A (flatten-list es)
flatten-all [] p = tt
flatten-all (e ∷ es) (p , ps) = p , flatten-all es ps

flatten-member : {e : C.Expr} {es : List C.Expr}
  → e ∈ es → flatten e ∈ flatten-list es
flatten-member first = first
flatten-member (later p) = later (flatten-member p)

-- This is only a pullback of the already implemented expression algorithm.
-- The comparator is not yet supplied by the reference system. Full closure
-- correspondence also needs normal-form decomposition and validity theorems.
module ClosureOnTerms (lt : C.Expr → C.Expr → Bool) where
  module Engine = C.Compute lt

  Closure : (Term → Set) → Term → Term → Set
  Closure A a d = Engine.C (λ e → A (flatten e)) (encode a) (encode d)

  seed : {A : Term → Set} (a d : Term) → A d
    → C.True (lt (encode d) (encode a)) → Closure A a d
  seed {A} a d ad p = Engine.seed (encode a) (encode d) transported p
    where
    transported : A (flatten (encode d))
    transported rewrite roundtrip d = ad

  -- Finite character now returns principal-sequence seeds, not Expr seeds.
  finite-character : {A : Term → Set} (a d : Term) → Closure A a d
    → Σ (List Term) (λ ts → Σ (All A ts) (λ _ → Closure (λ t → t ∈ ts) a d))
  finite-character a d p with Engine.finite-character (encode a) (encode d) p
  ... | es , covered , supported = flatten-list es , flatten-all es covered ,
    Engine.monotone-C (λ e → flatten-member) (encode a) (encode d) supported
