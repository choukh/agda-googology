```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where
open import WellFormed.Base
open import WellFormed.Properties
open import Lower using (_∘ⁿ_)
```

```agda
private instance
  _ = z≤
  _ = ≤-refl
  _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
  _ = _

variable i : Ord
```

```agda
Func↾ᴺᴸ : Type
Func↾ᴺᴸ = (a : Ord) ⦃ nl : NonLim a ⦄ → Ord
```

```agda
_↾ᴺᴸ : Func → Func↾ᴺᴸ
F ↾ᴺᴸ = λ a → F a
```

```agda
_inflatesᴺᴸ : Func↾ᴺᴸ → Type
F inflatesᴺᴸ = ∀ {x} → ⦃ nl : NonLim x ⦄ → x < F x
```

```agda
record Infl↾ᴺᴸ : Type where
  constructor infl↾ᴺᴸ
  field
    _[_] : Func↾ᴺᴸ
    inflᴺᴸ : _[_] inflatesᴺᴸ
```

```agda
record NormalInflᴺᴸ : Type where
  constructor normalInflᴺᴸ
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<
    inflᴺᴸ : (_[_] ↾ᴺᴸ) inflatesᴺᴸ
```

```agda
open Infl↾ᴺᴸ public
open NormalInflᴺᴸ public
```

```agda
iterω : NormalInflᴺᴸ → Infl↾ᴺᴸ
iterω ℱ = infl↾ᴺᴸ iter infl where
  fᵢ : (i : Ord) ⦃ nl : NonLim i ⦄ → Seq
  fᵢ i n = ((ℱ [_]) ∘ⁿ n) i
  instance w : ⦃ _ : NonLim i ⦄ → wf (fᵢ i)
  w {n = zero} = inflᴺᴸ ℱ
  w {n = suc n} = pres< ℱ w
  iter : Func↾ᴺᴸ
  iter i = lim (fᵢ i)
  infl : iter inflatesᴺᴸ
  infl {(zero)} = z<l
  infl {suc x} = map (lim {n = 1}) (inflᴺᴸ ℱ)
```

```agda

```
