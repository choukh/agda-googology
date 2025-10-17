{-# OPTIONS --safe --lossy-unification #-}
module OCF.Explore where

open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

data Ord₀ : Set where
  zero : Ord₀
  suc  : Ord₀ → Ord₀
  lim  : (f : ℕ → Ord₀) → Ord₀

private variable
  n : ℕ
  a b c i j ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Ord₀
  f g : ℕ → Ord₀

data _≤_ : Ord₀ → Ord₀ → Set where
  z≤  : zero ≤ a
  s≤s : a ≤ b → suc a ≤ suc b
  ≤l  : a ≤ f n → a ≤ lim f
  l≤  : (p : ∀ {n} → f n ≤ a) → lim f ≤ a

_<_ : Ord₀ → Ord₀ → Set
a < b = suc a ≤ b

l≤l : (∀ {n} → f n ≤ g n) → lim f ≤ lim g
l≤l p = l≤ (≤l p)

≤-refl : a ≤ a
≤-refl {a = zero} = z≤
≤-refl {a = suc _} = s≤s ≤-refl
≤-refl {a = lim _} = l≤l ≤-refl

≤-trans : a ≤ b → b ≤ c → a ≤ c
≤-trans z≤      q       = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
≤-trans p       (≤l q)  = ≤l (≤-trans p q)
≤-trans (l≤ p)  q       = l≤ (≤-trans p q)
≤-trans (≤l p)  (l≤ q)  = ≤-trans p q

≤s : a ≤ suc a
≤s {a = zero} = z≤
≤s {a = suc a} = s≤s ≤s
≤s {a = lim f} = l≤ (≤-trans ≤s (s≤s (≤l ≤-refl)))

f≤l : f n ≤ lim f
f≤l = ≤l ≤-refl

module _ (ℓ : Ord₀) (Ord≤ : (i : Ord₀) (p : i ≤ ℓ) → Set) where
  data Ordₛ : Set where
    zero  : Ordₛ
    suc   : Ordₛ → Ordₛ
    lim   : (f : ℕ → Ordₛ) → Ordₛ
    Lim   : (p : i ≤ ℓ) (F : Ord≤ i p → Ordₛ) → Ordₛ

module _ (Ordₙ : ℕ → Set) where
  data Ordₗ : Set where
    zero  : Ordₗ
    suc   : Ordₗ → Ordₗ
    lim   : (f : ℕ → Ordₗ) → Ordₗ
    Lim   : (n : ℕ) (F : Ordₙ n → Ordₗ) → Ordₗ

Ord≤ : (i : Ord₀) (p : i ≤ ℓ) → Set
Ord≤ zero _ = Ord₀
Ord≤ (suc i) (s≤s p) = Ordₛ i (λ j q → Ord≤ j (≤-trans q p))
Ord≤ (lim f) (l≤  p) = Ordₗ (λ n → Ord≤ (f n) p)
Ord≤ i (≤l p) = Ord≤ i p

Ord : Ord₀ → Set
Ord a = Ord≤ a ≤-refl

module _ {E₁ E₂ : (i : Ord₀) (p : i ≤ ℓ) → Set} (ih : ∀ {i} p → E₂ i p → E₁ i p) where
  morphₛ : Ordₛ ℓ E₁ → Ordₛ ℓ E₂
  morphₛ zero = zero
  morphₛ (suc a) = suc (morphₛ a)
  morphₛ (lim f) = lim (morphₛ ∘ f)
  morphₛ (Lim p F) = Lim p (morphₛ ∘ F ∘ (ih p))

module _ {E₁ E₂ : ℕ → Set} (ih : ∀ {n} → E₂ n → E₁ n) where
  morphₗ : Ordₗ E₁ → Ordₗ E₂
  morphₗ zero = zero
  morphₗ (suc a) = suc (morphₗ a)
  morphₗ (lim f) = lim (morphₗ ∘ f)
  morphₗ (Lim n F) = Lim n (morphₗ ∘ F ∘ ih)

morph : {p : i ≤ ℓ₁} {q : i ≤ ℓ₂} → Ord≤ i p → Ord≤ i q
morph {i = zero} = id
morph {i = suc _} {p = s≤s p} {q = s≤s q} = morphₛ (λ r → morph {p = ≤-trans r q} {q = ≤-trans r p})
morph {i = lim _} {p = l≤ p}  {q = l≤ q}  = morphₗ (morph {p = q} {q = p})
morph {i = suc _} {p = ≤l p}  {q = q}     = morph {p = p} {q = q}
morph {i = suc _} {p = p}     {q = ≤l q}  = morph {p = p} {q = q}
morph {i = lim _} {p = ≤l p}  {q = q}     = morph {p = p} {q = q}
morph {i = lim _} {p = p}     {q = ≤l q}  = morph {p = p} {q = q}

↑₀ˢ : {p : i ≤ ℓ} → Ord₀ → Ord≤ (suc i) (s≤s p)
↑₀ˢ zero = zero
↑₀ˢ (suc a) = suc (↑₀ˢ a)
↑₀ˢ (lim f) = lim (↑₀ˢ ∘ f)

↑ₛˢ : {p : i ≤ ℓ₁} {q : suc i ≤ ℓ₂}
  → Ord≤ (suc i) (s≤s p) → Ord≤ (suc (suc i)) (s≤s q)
↑ₛˢ zero = zero
↑ₛˢ (suc a) = suc (↑ₛˢ a)
↑ₛˢ (lim f) = lim (↑ₛˢ ∘ f)
↑ₛˢ a@(Lim p F) = Lim (≤-trans p ≤s) (↑ₛˢ ∘ F ∘ morph)

↑ₗˢ : {p : ∀ {n} → f n ≤ ℓ₁} {q : lim f ≤ ℓ₂}
  → Ord≤ (lim f) (l≤ p) → Ord≤ (suc (lim f)) (s≤s q)
↑ₗˢ zero = zero
↑ₗˢ (suc a) = suc (↑ₗˢ a)
↑ₗˢ (lim f) = lim (↑ₗˢ ∘ f)
↑ₗˢ (Lim n F) = Lim f≤l (↑ₗˢ ∘ F ∘ morph)

↑ˢ : {p : i ≤ ℓ₁} {q : i ≤ ℓ₂} → Ord≤ i p → Ord≤ (suc i) (s≤s q)
↑ˢ {i = zero}               = ↑₀ˢ
↑ˢ {i = suc i} {p = s≤s p}  = ↑ₛˢ
↑ˢ {i = lim f} {p = l≤ p}   = ↑ₗˢ
↑ˢ {i = suc i} {p = ≤l p}   = ↑ˢ {p = p}
↑ˢ {i = lim f} {p = ≤l p}   = ↑ˢ {p = p}

↑₀ˡ : {p : ∀ {n} → f n ≤ ℓ} → Ord₀ → Ord≤ (lim f) (l≤ p)
↑₀ˡ zero = zero
↑₀ˡ (suc a) = suc (↑₀ˡ a)
↑₀ˡ (lim f) = lim (↑₀ˡ ∘ f)

module _ (eq : f n ≡ suc i) where
  ↑ₛˡ : {p : i ≤ ℓ₁} {q : ∀ {n} → f n ≤ ℓ₂} → Ord≤ (suc i) (s≤s p) → Ord≤ (lim f) (l≤ q)
  ↑ₛˡ zero = zero
  ↑ₛˡ (suc a) = suc (↑ₛˡ a)
  ↑ₛˡ (lim f) = lim (↑ₛˡ ∘ f)
  ↑ₛˡ (Lim p F) = Lim n (λ x → ↑ₛˡ (F {!   !}))

module _ (eq : f n ≡ lim g) where
  ↑ₗˡ : {p : ∀ {n} → g n ≤ ℓ₁} {q : ∀ {n} → f n ≤ ℓ₂} → Ord≤ (lim g) (l≤ p) → Ord≤ (lim f) (l≤ q)
  ↑ₗˡ zero = zero
  ↑ₗˡ (suc a) = suc (↑ₗˡ a)
  ↑ₗˡ (lim f) = lim (↑ₗˡ ∘ f)
  ↑ₗˡ (Lim m F) = Lim n (λ x → ↑ₗˡ (F {!   !}))

↑ˡ : {p : f n ≤ ℓ₁} {q : ∀ {n} → f n ≤ ℓ₂} → Ord≤ (f n) p → Ord≤ (lim f) (l≤ q)
↑ˡ {f} {n} with f n in eq
↑ˡ              | zero = ↑₀ˡ
↑ˡ {p = s≤s p}  | suc _ = ↑ₛˡ eq
↑ˡ {p = l≤ p}   | lim _ = ↑ₗˡ eq
↑ˡ {p = ≤l p}   | suc _ rewrite sym eq = ↑ˡ
↑ˡ {p = ≤l p}   | lim _ rewrite sym eq = ↑ˡ

Ω : (ℓ : Ord₀) → Ord ℓ
Ω zero = suc zero
Ω (suc i) = Lim ≤-refl ↑ˢ
Ω (lim f) = lim (λ n → ↑ˡ (Ω (f n)))
