
```agda
module Madore.OneΩ where
open import Base public
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
F ∘^₁ suc a = F ∘ (F ∘^₁ a)
F ∘^₁ lim α[_] = λ b → lim λ n → (F ∘^₁ α[ n ]) b
F ∘^₁ Lim a[_] = λ b → Lim λ α → (F ∘^₁ a[ α ]) b
```

```agda
_+₁_ = λ a b → (suc ∘^₁ b) a      ; infixl 6 _+₁_
_*₁_ = λ a b → ((_+₁ a) ∘^₁ b) 0  ; infixl 7 _*₁_
_^₁_ = λ a b → ((_* a) ∘^ b) 1    ; infixr 8 _^₁_
```

```agda
ψ : Ord₁ → Ord
ψ zero = lfp (ω ^_)
ψ (suc a) = lfp (ψ a ^_)
ψ (lim a[_]) = lim λ n → ψ a[ n ]
ψ (Lim a[_]) = lfp λ α → ψ a[ α ]
```
