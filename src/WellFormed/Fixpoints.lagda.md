```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
private variable
  i : Ord
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
isFix : Func → Ord → Type
isFix F a = a ≡ F a
```

```agda
isFix-iterω : (F : Func) (i : Ord) (w : wf (F ⟨ i ⟩∘ⁿ)) → isFix F (iterω F i w)
isFix-iterω F i w = {!   !}
```

```agda
ε₀ : Ord
ε₀ = iterω (ω^ [_]) 0 w where
  w : wf (ω^ [_] ⟨ 0 ⟩∘ⁿ)
  w {(zero)} = zero₁
  w {suc n} = pres< ω^ w
```

```agda
ε₁ : Ord
ε₁ = iterω (ω^ [_]) (suc ε₀) w where
  w : wf ((ω^ [_]) ⟨ suc ε₀ ⟩∘ⁿ)
  w {(zero)} = begin-strict
    suc ε₀          ≈⟨ cong suc {!   !} ⟩
    suc (ω^ [ ε₀ ]) <⟨ {!   !} ⟩
    ω^ [ suc ε₀ ]   ∎ where open SubTreeReasoning
  w {suc n} = pres< ω^ w
```