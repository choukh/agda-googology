```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import Lower using (_∘ⁿ_)
open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
private
  instance
    _ = z≤
    _ = ≤-refl
    _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
    _ = _
  variable
    i : Ord
```

```agda
record NormalInflNL : Type where
  constructor normalInflNL
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<
    infl< : (_[_] ↾ NonLim) inflates _<_ within NonLim
open NormalInflNL public
```

```agda
iterω : NormalInflNL → Infl↾ NonLim
iterω ℱ = mkInfl↾ iter infl where
  fᵢ : (i : Ord) ⦃ nl : NonLim i ⦄ → Seq
  fᵢ i n = ((ℱ [_]) ∘ⁿ n) i
  instance w : ⦃ _ : NonLim i ⦄ → wf (fᵢ i)
  w {n = zero} = infl< ℱ
  w {n = suc n} = pres< ℱ w
  iter : Func↾ NonLim
  iter i = lim (fᵢ i)
  infl : iter inflates _<_ within NonLim
  infl {(zero)} = z<l
  infl {suc x} = map (lim {n = 1}) (infl< ℱ)
```
