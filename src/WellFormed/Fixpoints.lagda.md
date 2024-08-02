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
  init  : Domain F i i
  fix   : Domain F i j → (w : wf (F ⟨ j ⟩∘ⁿ)) → Domain F i (iterω F j w)
  jump  : Domain F i j → Domain F i (suc j)

syntax Domain F i j = j ∈Dom⟨ F , i ⟩
```

```agda
record Fixable (i : Ord) : Type where
  constructor mkFixable
  field
    func  : Func
    wff   : Domain func i j → wf (F ⟨ j ⟩∘ⁿ)
    infl< : (func ↾ Domain func i) inflates _<_ within _
```

```agda
module _ (ℱ : Fixable i) where
  open Fixable ℱ
```

```agda
  fixpt : Func
  inDom : ∀ a → fixpt a ∈Dom⟨ func , i ⟩

  fixpt zero = iterω func i (wff init)
  fixpt (suc a) = iterω func (suc (fixpt a)) (wff (jump (inDom a)))
  fixpt (lim f) = lim (λ n → fixpt (f n)) ⦃ {!   !} ⦄

  inDom zero = fix init (wff init)
  inDom (suc a) = fix (jump (inDom a)) (wff (jump (inDom a)))
  inDom (lim f) = {!   !}
```
