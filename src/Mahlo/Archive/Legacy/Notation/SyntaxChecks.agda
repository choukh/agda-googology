{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Notation.SyntaxChecks where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Notation.FiniteSupport using (Dec; yes; no; Empty)
open import Mahlo.Archive.Legacy.Notation.Syntax
open import Mahlo.Archive.Legacy.Notation.SyntaxBridge using (encode; flatten; canonicalize)
import Mahlo.Archive.Legacy.Notation.Closure as C

Accepts : {P : Set} → Dec P → Set
Accepts (yes _) = ⊤
Accepts (no _) = Empty

Rejects : {P : Set} → Dec P → Set
Rejects (yes _) = Empty
Rejects (no _) = ⊤

psi-zero-rejected : Rejects (raw? (single (psi nil nil)))
psi-zero-rejected = tt

psi-mahlo-accepted : Accepts (raw? (single (psi (single mahlo) nil)))
psi-mahlo-accepted = tt

omega-one-regular : Accepts (regular? (single (omega one)))
omega-one-regular = tt

-- Ω0 belongs to T' but cannot index psi. It is also excluded by OT rule 5;
-- raw? intentionally checks T' only, so it accepts Ω0 itself.
omega-zero-raw : Accepts (raw? (single (omega nil)))
omega-zero-raw = tt

omega-zero-not-regular : Rejects (regular? (single (omega nil)))
omega-zero-not-regular = tt

psi-omega-zero-rejected : Rejects (raw? (single (psi (single (omega nil)) nil)))
psi-omega-zero-rejected = tt

i₁ i₂ : Term
i₁ = single (psi (single mahlo) nil)
i₂ = single (psi i₁ nil)

first-collapse-in-I : isI i₁ ≡ true
first-collapse-in-I = refl

second-collapse-in-Fi : isFi i₂ ≡ true
second-collapse-in-Fi = refl

second-collapse-not-in-I : isI i₂ ≡ false
second-collapse-not-in-I = refl

-- Being in Fi' is not sufficient to be a psi index in R'.
second-collapse-not-regular : Rejects (regular? i₂)
second-collapse-not-regular = tt

successor-tail : isSuccessor (cons mahlo (cons (phi nil nil) nil)) ≡ true
successor-tail = refl

nonsuccessor-tail : isSuccessor (cons (phi nil nil) (cons mahlo nil)) ≡ false
nonsuccessor-tail = refl

-- Principal sequences preserve order of entries; flattening is not sorting.
order-preserved : flatten (C.add C.mahlo (C.phi C.zero C.zero))
  ≡ cons mahlo (cons (phi nil nil) nil)
order-preserved = refl

sequence-distinct : Rejects (term≟
  (cons mahlo (cons (phi nil nil) nil))
  (cons (phi nil nil) (cons mahlo nil)))
sequence-distinct = tt

no-trailing-zero : encode (single mahlo) ≡ C.mahlo
no-trailing-zero = refl

flatten-association : canonicalize (C.add (C.add C.mahlo C.mahlo) C.mahlo)
  ≡ C.add C.mahlo (C.add C.mahlo C.mahlo)
flatten-association = refl
