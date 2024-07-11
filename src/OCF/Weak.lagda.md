
```agda
module OCF.Weak where
open import Base public
```

```agda
data Ord₁ : Set where
  zero₁ : Ord₁
  suc₁  : Ord₁ → Ord₁
  lim₁  : (ℕ → Ord₁) → Ord₁
  Lim₁ : (Ord → Ord₁) → Ord₁
```

```agda
finord₁ : ℕ → Ord₁
finord₁ n = (suc₁ ∘ⁿ n) zero₁

ω₁ : Ord₁
ω₁ = lim₁ finord₁
```

```agda
instance
  nOrd₁ = Number Ord₁ ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord₁ n }
```

```agda
_↑₁ : Ord → Ord₁
zero ↑₁ = zero₁
suc α ↑₁ = suc₁ (α ↑₁)
lim f ↑₁ = lim₁ λ n → f n ↑₁
```

```agda
Ω₁ : Ord₁
Ω₁ = Lim₁ _↑₁
```

```agda
ψ : Ord₁ → Ord
ψ zero₁ = 1
ψ (suc₁ α₁) = suc (ψ α₁)
ψ (lim₁ f₁) = lim λ n → ψ (f₁ n)
ψ (Lim₁ F₁) = lim λ n → ((λ α → ψ (F₁ α)) ∘ⁿ n) 0
```
