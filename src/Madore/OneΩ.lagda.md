
```agda
module Madore.OneΩ where
open import Base
```

```agda
data Ord₁ : Set where
  zero : Ord₁
  suc  : Ord₁ → Ord₁
  lim  : (ℕ → Ord₁) → Ord₁
  Lim : (Ord → Ord₁) → Ord₁
```

```agda
finord₁ : ℕ → Ord₁
finord₁ n = (suc ∘ⁿ n) zero

ω₁ : Ord₁
ω₁ = lim finord₁
```

```agda
instance
  nOrd₁ = Number Ord₁ ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord₁ n }
```

```agda
_↑₁ : Ord → Ord₁
zero ↑₁ = zero
suc α ↑₁ = suc (α ↑₁)
lim f ↑₁ = lim λ n → f n ↑₁
```

```agda
Ω₁ : Ord₁
Ω₁ = Lim _↑₁
```

```agda
_∘^₁_ : (Ord₁ → Ord₁) → Ord₁ → Ord₁ → Ord₁
F ∘^₁ zero = id
F ∘^₁ suc x = F ∘ (F ∘^₁ x)
F ∘^₁ lim α[_] = λ y → lim λ n → (F ∘^₁ α[ n ]) y
F ∘^₁ Lim x[_] = λ y → Lim λ α → (F ∘^₁ x[ α ]) y
```

```agda
_+₁_ = λ x y → (suc ∘^₁ y) x      ; infixl 6 _+₁_
_*₁_ = λ x y → ((_+₁ x) ∘^₁ y) 0  ; infixl 7 _*₁_
_^₁_ = λ x y → ((_* x) ∘^ y) 1    ; infixr 8 _^₁_
```

```agda
ψ : Ord₁ → Ord
ψ zero = lfp (ω ^_)
ψ (suc x) = lfp (ψ x ^_)
ψ (lim x[_]) = lim λ n → ψ x[ n ]
ψ (Lim x[_]) = lfp λ α → ψ x[ α ]
```
