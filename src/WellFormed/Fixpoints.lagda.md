```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
data Domain : Ord → Type
ω^_ : Domain a → Ord

data Domain where
  zero : Domain zero
  suc  : Domain a → Domain (suc a)
  lim  : ⦃ _ : wf f ⦄ (ḟ : ∀ n → Domain (f n)) (r : f 0 < ω^ ḟ 0) → Domain (lim f)
```

```agda
private variable ȧ : Domain a
ω^-nz : NonZero (ω^ ȧ)
ω^-pres-rd : {ȧ : Domain a} {ḃ : Domain b} → Road a b → Road (ω^ ȧ) (ω^ ḃ)

ω^-pres< : {ȧ : Domain a} {ḃ : Domain b} → a < b → ω^ ȧ < ω^ ḃ
ω^-pres< = map ω^-pres-rd
```

```agda
ω^ zero = 1
ω^ (suc ȧ) = (ω^ ȧ * ω) ⦃ ω^-nz ⦄
ω^ (lim {f} ḟ r) = lim homo
  module BaseOmega where
  homo : Seq
  homo zero = f 0
  homo (suc n) = ω^ ḟ n
  instance homo-wf : wf homo
  homo-wf {(zero)} = r
  homo-wf {suc n} = ω^-pres< it

ω^-nz {ȧ = zero}    = _
ω^-nz {ȧ = suc ȧ}   = _
ω^-nz {ȧ = lim ḟ r} = _

ω^-pres-rd zero = {!   !}
ω^-pres-rd (suc r) = {!   !}
ω^-pres-rd (lim r) = {!   !}
```
