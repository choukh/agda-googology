```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
IsZero : Ord → Type
IsZero zero = ⊤
IsZero (suc _) = ⊥
IsZero (lim _) = ⊥
```

```agda
HeadZero : Ord → Type
HeadZero zero = ⊤
HeadZero (suc a) = ⊤
HeadZero (lim f) = IsZero (f 0)
```

```agda
ω^_ : (a : Ord) → ⦃ HeadZero a ⦄ → Ord
ω^-nz : ⦃ _ : HeadZero a ⦄ → NonZero (ω^ a)
ω^-pres-rd : ω^_ preserves Road

ω^-pres< : ω^_ preserves _<_
ω^-pres< = map ω^-pres-rd
```

```agda
ω^ zero = 1
ω^ suc a = (ω^ a * ω) ⦃ ω^-nz ⦄
ω^ lim f = lim (homo f) ⦃ {!   !} ⦄
  module BaseOmega where
  homo : Seq → Seq
  homo f zero = f 0
  homo f (suc n) = ω^ f n
  homo-wf : wf (homo f)
  homo-wf {(zero)} = {!   !}
  homo-wf {suc n} = {!   !}

ω^-nz {(zero)} = _
ω^-nz {suc a} = _
ω^-nz {lim f} = _

ω^-pres-rd = {!   !}
```
