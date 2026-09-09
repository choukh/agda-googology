{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Fundamental.MahloChecks where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Notation.Syntax
import Mahlo.Archive.Legacy.Notation.Reference as R
open import Mahlo.Archive.Legacy.Fundamental.Mahlo

ω : Term
ω = single (phi nil one)

two : Term
two = append one one

zero-valid : R.validOT nil ≡ just true
zero-valid = refl

omega-valid : R.validOT ω ≡ just true
omega-valid = refl

omega-zero-invalid : R.validOT (single (omega nil)) ≡ just false
omega-zero-invalid = refl

omega-mahlo-invalid : R.validOT (single (omega (single mahlo))) ≡ just false
omega-mahlo-invalid = refl

one-before-omega : R.less one ω ≡ just true
one-before-omega = refl

omega-not-before-one : R.less ω one ≡ just false
omega-not-before-one = refl

unsorted-sum-invalid : R.validOT (append one ω) ≡ just false
unsorted-sum-invalid = refl

sorted-sum-valid : R.validOT (append ω one) ≡ just true
sorted-sum-valid = refl

psi-mahlo-valid : R.validOT (single (psi (single mahlo) nil)) ≡ just true
psi-mahlo-valid = refl

nested-psi-valid : R.validOT (single (psi (single (psi (single mahlo) nil)) one)) ≡ just true
nested-psi-valid = refl

support-below-mahlo : R.SC 100 (single mahlo) (single (psi (single mahlo) nil))
  ≡ just (single (psi (single mahlo) nil) ∷ [])
support-below-mahlo = refl

zero-sequence : basicSequence nil 3 ≡ ok nil
zero-sequence = refl

successor-sequence : basicSequence two 7 ≡ ok one
successor-sequence = refl

omega-sequence-2 : basicSequence ω 2 ≡ ok one
omega-sequence-2 = refl

omega-sequence-3 : basicSequence ω 3 ≡ ok two
omega-sequence-3 = refl

reject-uncountable : basicSequence omega₁ 2 ≡ invalid
reject-uncountable = refl

endpoint-zero : endpointSequence 0 ≡ ok (stage 0)
endpoint-zero = refl

endpoint-one : endpointSequence 1 ≡ ok (stage 1)
endpoint-one = refl

endpoint-two : endpointSequence 2 ≡ ok (stage 2)
endpoint-two = refl

first-stages-increase : R.less (stage 0) (stage 1) ≡ just true
first-stages-increase = refl

-- Locks the explicit equality convention in Reference.GP, not a source theorem.
support-at-index : R.G 100 (single (psi (single mahlo) nil))
  (single (psi (single mahlo) nil)) ≡ just (nil ∷ [])
support-at-index = refl

exhaustion-is-not-false : R.lt 0 nil one ≡ nothing
exhaustion-is-not-false = refl
