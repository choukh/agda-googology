```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
private variable
  i j : Ord
```

```agda
open import Lower using (_∘ⁿ_)
_⟨_⟩∘ⁿ : Func → (i : Ord) → Seq
(F ⟨ i ⟩∘ⁿ) n = (F ∘ⁿ n) i
```

```agda
iterω : (F : Func) (i : Ord) (w : wf (F ⟨ i ⟩∘ⁿ)) → Ord
iterω F i w = lim (F ⟨ i ⟩∘ⁿ) ⦃ w ⦄
```

```agda
data Domain (F : Func) (i : Ord) : Ord → Type where
  zero  : Domain F i i
  fixpt : Domain F i j → (w : wf (F ⟨ j ⟩∘ⁿ)) → Domain F i (iterω F j w)
  jump  : Domain F i j → Domain F i (suc j)
```

```agda
record Fixable (i : Ord) : Type where
  constructor mkFixable
  field
    _[_]  : Func
    wff   : Domain _[_] i j → wf (F ⟨ j ⟩∘ⁿ)
    infl< : (_[_] ↾ Domain _[_] i) inflates _<_ within _
open Fixable public
```

```agda
module _ (i : Ord) where
  _′ : (ℱ : Fixable i) → Func
  domain : (ℱ : Fixable i) (a : Ord) → Domain (ℱ [_]) i ((ℱ ′) a)

  (ℱ ′) zero = iterω (ℱ [_]) i (wff ℱ zero)
  (ℱ ′) (suc a) = iterω (ℱ [_]) (suc ((ℱ ′) a)) (wff ℱ (jump (domain ℱ a)))
  (ℱ ′) (lim f) = {!   !}

  domain ℱ zero = fixpt zero (wff ℱ zero)
  domain ℱ (suc a) = fixpt (jump (domain ℱ a)) (wff ℱ (jump (domain ℱ a)))
  domain ℱ (lim f) = {!   !}
```
