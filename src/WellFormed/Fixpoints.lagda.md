```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
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
  fixpt : Domain F i a → (w : wf (F ⟨ a ⟩∘ⁿ)) → Domain F i (iterω F a w)
  jump  : Domain F i a → Domain F i (suc a)
```

```agda

```
