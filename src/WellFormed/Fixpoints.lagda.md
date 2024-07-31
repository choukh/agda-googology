```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where
open import WellFormed.Base
open import WellFormed.Properties
```

```agda
private instance
  _ = ≤-refl
  _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
  _ = _
```

```agda
iterω : EverInfl i → EverInfl i
iterω ℱ = ℱ ^⟨ ω ⟩
```

```agda
_∘Suc : EverInfl i → EverInfl i
ℱ ∘Suc = everInfl (λ x ⦃ i≤ ⦄ → (ℱ [ suc x ]) ⦃ ≤-trans i≤ (inl zero₁) ⦄)
  λ {x} ⦃ i≤ ⦄ → {! infl< ℱ {suc x} !}
```

```agda
jump⟨_⟩ : (i : Ord) (ℱ : EverInfl i) → ⦃ i ≤ ℱ [ i ] ⦄ → Normal
jump⟨ i ⟩ ℱ = ℱ ∘Suc ⟨ ℱ [ i ] ⟩^
```

```agda
--jump : (ℱ : Iterable) → Normal
```
