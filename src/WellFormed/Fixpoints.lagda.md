```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
open import Lower using (_∘ⁿ_)
itn : Func → Ord → Seq
itn F i n = (F ∘ⁿ n) i
```

```agda
itω : (F : Func) (i : Ord) (w : wf (itn F i)) → Ord
itω F i w = lim (itn F i) ⦃ w ⦄
```

```agda
_+ω^_ : Ord → Ord → Ord
ω^ : Func
ω^ a = 0 +ω^ a
```

```agda
+ω^-infl-rd : (_+ω^ b) inflates Road
+ω^-infl : (_+ω^ b) inflates _<_
+ω^-infl = ∣ +ω^-infl-rd ∣₁
```

```agda
ω^-pres-rd : (a +ω^_) preserves Road
ω^-pres : (a +ω^_) preserves _<_
ω^-pres = map ω^-pres-rd
```

```agda
a +ω^ zero = suc a
a +ω^ suc b = itω (_+ω^ b) a +ω^-infl
a +ω^ lim f = lim (λ n → a +ω^ f n) ⦃ ω^-pres it ⦄
```

```agda
+ω^-infl-rd {(zero)} = zero
+ω^-infl-rd {suc b} = rd[ 1 ] +ω^-infl-rd
+ω^-infl-rd {lim f} = rd[ 0 ] +ω^-infl-rd
```

```agda
ω^-pres-rd zero        = rd[ 2 ] +ω^-infl-rd
ω^-pres-rd (suc r)     = rd[ 1 ] $ ω^-pres-rd r
ω^-pres-rd (lim {n} r) = rd[ n ] $ ω^-pres-rd r
```

```agda
record Fixable : Type where
  constructor mkFixable
  field _⟨_⟩ : Func
  private F = _⟨_⟩
  field
    fix-pres : F preserves _<_
    ⦃ fix-nz ⦄ : NonZero (F 0)

  instance
    fix-suc-nz : NonZero (F (suc a))
    fix-suc-nz = nz-intro $         begin-strict
      0                             ≤⟨ z≤ ⟩
      F _                           <⟨ fix-pres zero₁ ⟩
      F (suc _)                     ∎ where open SubTreeReasoning
```

```agda
module Fixpt (ℱ : Fixable) where
  open Fixable ℱ renaming (_⟨_⟩ to F)

  F′ : Func
  F′-pres-rd : F′ preserves Road
  F′-pres : F′ preserves _<_
  F′-pres = map F′-pres-rd
```

```agda
  F′ zero = itω F 0 w
    module FixptZero where
    w : wf (itn F 0)
    w {(zero)} = nz-elim
    w {suc n} = fix-pres w
  F′ (suc a) = itω (λ x → i + F x) i w
    module FixptSuc where
    i = suc (F′ a)
    w : wf (itn (λ x → i + F x) i)
    w {n = zero} = +-infl
    w {n = suc n} = +-pres (fix-pres w)
  F′ (lim f) = lim (λ n → F′ (f n)) ⦃ F′-pres it ⦄
```

```agda
  F′-pres-rd {(x)} zero = rd[ 0 ] zero
  F′-pres-rd {(x)} (suc r) = rd[ 0 ] $ rd-trans (F′-pres-rd r) zero
  F′-pres-rd {(x)} (lim {n} r) = rd[ n ] $ F′-pres-rd r
```

```agda
fixpt : Fixable → Fixable
fixpt ℱ = mkFixable F′ F′-pres ⦃ _ ⦄ where open Fixpt ℱ
```

```agda
base-ω : Fixable
base-ω = mkFixable ω^ ω^-pres
```

```agda
ε ζ η : Fixable
ε = fixpt base-ω
ζ = fixpt ε
η = fixpt ζ
```

```agda
open Fixable public

ε-0 : ε ⟨ 0 ⟩ ≡ itω ω^ 0 _
ε-0 = refl

ε-suc : ε ⟨ suc a ⟩ ≡ itω (λ x → suc (ε ⟨ a ⟩) + ω^ x) (suc (ε ⟨ a ⟩)) _
ε-suc = refl

ε-lim : {w : wf f} → ε ⟨ lim f ⦃ w ⦄ ⟩ ≡ lim- λ n → ε ⟨ f n ⟩
ε-lim = refl
```
