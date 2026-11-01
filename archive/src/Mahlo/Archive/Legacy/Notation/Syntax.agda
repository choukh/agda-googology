{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Notation.Syntax where

-- Ambient syntax and the decidable T' formation rules of Setzer, Mahlo,
-- Definition 3.2. T' is NOT OT: Definition 3.6 adds order/closure conditions.
-- A term is a sequence of principals: empty = 0, singleton = its principal.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Notation.FiniteSupport using (Dec; yes; no; Empty)

mutual
  data Term : Set where
    nil : Term
    cons : Principal → Term → Term

  data Principal : Set where
    phi : Term → Term → Principal
    psi : Term → Term → Principal
    omega : Term → Principal
    mahlo : Principal

single : Principal → Term
single p = cons p nil

one : Term
one = single (phi nil nil)

append : Term → Term → Term
append nil b = b
append (cons p a) b = cons p (append a b)

-- Syntactic class tags only. Membership in the reference classes also
-- requires Raw below. No ordinal inequality is inferred from these tags.
isSuccessor : Term → Bool
isSuccessor nil = false
isSuccessor (cons (phi nil nil) nil) = true
isSuccessor (cons _ nil) = false
isSuccessor (cons _ (cons p ps)) = isSuccessor (cons p ps)

isI : Term → Bool
isI (cons mahlo nil) = true
isI (cons (psi (cons mahlo nil) _) nil) = true
isI _ = false

isRegular : Term → Bool
isRegular (cons mahlo nil) = true
isRegular (cons (psi (cons mahlo nil) _) nil) = true
isRegular (cons (omega a) nil) = isSuccessor a
isRegular _ = false

isFi : Term → Bool
isFi (cons mahlo nil) = true
isFi (cons (psi (cons mahlo nil) _) nil) = true
isFi (cons (psi k _) nil) = isI k
isFi _ = false

isCardinal : Term → Bool
isCardinal (cons (omega (cons _ _)) nil) = true
isCardinal a = isFi a

isG : Term → Bool
isG (cons mahlo nil) = true
isG (cons (omega _) nil) = true
isG (cons (psi _ _) nil) = true
isG _ = false

True : Bool → Set
True true = ⊤
True false = Empty

-- A separate predicate keeps evidence out of the syntax. In particular,
-- equality of codes never needs equality of regularity certificates.
mutual
  Raw : Term → Set
  Raw nil = ⊤
  Raw (cons p ps) = Σ (RawP p) (λ _ → Raw ps)

  RawP : Principal → Set
  RawP (phi a b) = Σ (Raw a) (λ _ → Raw b)
  RawP (psi k b) = Σ (Raw k) (λ _ → Σ (Raw b) (λ _ → True (isRegular k)))
  RawP (omega a) = Raw a
  RawP mahlo = ⊤

Regular : Term → Set
Regular a = Σ (Raw a) (λ _ → True (isRegular a))

true? : (b : Bool) → Dec (True b)
true? true = yes tt
true? false = no (λ x → x)

pair? : {A B : Set} → Dec A → Dec B → Dec (Σ A (λ _ → B))
pair? (yes p) (yes q) = yes (p , q)
pair? (yes p) (no q) = no (λ r → q (snd r))
pair? (no p) q = no (λ r → p (fst r))

mutual
  raw? : (a : Term) → Dec (Raw a)
  raw? nil = yes tt
  raw? (cons p ps) = pair? (rawP? p) (raw? ps)

  rawP? : (p : Principal) → Dec (RawP p)
  rawP? (phi a b) = pair? (raw? a) (raw? b)
  rawP? (psi k b) = pair? (raw? k) (pair? (raw? b) (true? (isRegular k)))
  rawP? (omega a) = raw? a
  rawP? mahlo = yes tt

regular? : (a : Term) → Dec (Regular a)
regular? a = pair? (raw? a) (true? (isRegular a))

psi-index-regular : (k b : Term) → RawP (psi k b) → Regular k
psi-index-regular k b (rk , rb , regular) = rk , regular

raw-append : (a b : Term) → Raw a → Raw b → Raw (append a b)
raw-append nil b ra rb = rb
raw-append (cons p ps) b (rp , rps) rb = rp , raw-append ps b rps rb

-- Unique decomposition by shape; no binary sum constructor and no explicit
-- zero/singleton sum nodes can introduce multiple spellings of a sequence.
data View : Term → Set where
  zero-view : View nil
  principal-view : (p : Principal) → View (single p)
  sum-view : (p q : Principal) (tail : Term) → View (cons p (cons q tail))

view : (a : Term) → View a
view nil = zero-view
view (cons p nil) = principal-view p
view (cons p (cons q tail)) = sum-view p q tail

-- Decidable syntactic equality, needed before implementing the simultaneous
-- reference comparison/support recursion. This is not ordinal equality.
private
  congruence : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  congruence f refl = refl

  head : Term → Principal
  head nil = mahlo
  head (cons p ps) = p

  tail : Term → Term
  tail nil = nil
  tail (cons p ps) = ps

  arg₁ : Principal → Term
  arg₁ (phi a b) = a
  arg₁ (psi k b) = k
  arg₁ (omega a) = a
  arg₁ mahlo = nil

  arg₂ : Principal → Term
  arg₂ (phi a b) = b
  arg₂ (psi k b) = b
  arg₂ (omega a) = nil
  arg₂ mahlo = nil

mutual
  term≟ : (a b : Term) → Dec (a ≡ b)
  term≟ nil nil = yes refl
  term≟ nil (cons q qs) = no (λ ())
  term≟ (cons p ps) nil = no (λ ())
  term≟ (cons p ps) (cons q qs) with principal≟ p q
  ... | no neq = no (λ eq → neq (congruence head eq))
  ... | yes refl with term≟ ps qs
  ...   | no neq = no (λ eq → neq (congruence tail eq))
  ...   | yes refl = yes refl

  principal≟ : (p q : Principal) → Dec (p ≡ q)
  principal≟ mahlo mahlo = yes refl
  principal≟ mahlo (phi _ _) = no (λ ())
  principal≟ mahlo (psi _ _) = no (λ ())
  principal≟ mahlo (omega _) = no (λ ())
  principal≟ (phi _ _) mahlo = no (λ ())
  principal≟ (phi _ _) (psi _ _) = no (λ ())
  principal≟ (phi _ _) (omega _) = no (λ ())
  principal≟ (psi _ _) mahlo = no (λ ())
  principal≟ (psi _ _) (phi _ _) = no (λ ())
  principal≟ (psi _ _) (omega _) = no (λ ())
  principal≟ (omega _) mahlo = no (λ ())
  principal≟ (omega _) (phi _ _) = no (λ ())
  principal≟ (omega _) (psi _ _) = no (λ ())
  principal≟ (phi a b) (phi c d) with term≟ a c
  ... | no neq = no (λ eq → neq (congruence arg₁ eq))
  ... | yes refl with term≟ b d
  ...   | no neq = no (λ eq → neq (congruence arg₂ eq))
  ...   | yes refl = yes refl
  principal≟ (psi k b) (psi l d) with term≟ k l
  ... | no neq = no (λ eq → neq (congruence arg₁ eq))
  ... | yes refl with term≟ b d
  ...   | no neq = no (λ eq → neq (congruence arg₂ eq))
  ...   | yes refl = yes refl
  principal≟ (omega a) (omega b) with term≟ a b
  ... | no neq = no (λ eq → neq (congruence arg₁ eq))
  ... | yes refl = yes refl
