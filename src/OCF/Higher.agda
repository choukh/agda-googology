{-# OPTIONS --safe --without-K --lossy-unification #-}

module OCF.Higher where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO
open Nat using (n) renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open Ordᴰ using (Ordᴰ; _<_; cumsum; cumsum-mono)
open Ord_ord using (Ord; Ord₀; Ord₊; ℓ; coe; coe₀; ↑; Ω; _+_; lfp; ψ<; ψⁿ; ψ₀;ordᴰ)
open _<ᴺ_ ; open _<_; open Ord₊

ψᴰ : ℕ → Ordᴰ
ψᴰ = cumsum (ordᴰ ∘ ψⁿ)

data OrdΩ : Set where
  zero  : OrdΩ
  suc   : OrdΩ → OrdΩ
  lim   : (f : ℕ → OrdΩ) → OrdΩ
  limₙ  : (p : ℓ < ψᴰ n) (f : Ord ℓ → OrdΩ) → OrdΩ

↑Ω : Ord (ψᴰ n) → OrdΩ
↑Ω zero = zero
↑Ω (suc a) = suc (↑Ω a)
↑Ω (lim f) = lim (↑Ω ∘ f)
↑Ω (limᵢ p f) = limₙ p (↑Ω ∘ f ∘ coe₀)

ΩΩ : OrdΩ
ΩΩ = lim (λ n → limₙ {ℓ = ψᴰ n} (cumsum-mono (ordᴰ ∘ ψⁿ) zero) ↑Ω)

ψ<Ω : OrdΩ → Ord (ψᴰ n)
ψ<Ω zero = Ω _
ψ<Ω (suc a) = lfp (ψ<Ω a +_)
ψ<Ω (lim f) = lim (ψ<Ω ∘ f)
ψ<Ω {n} (limₙ {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<Ω ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<Ω ∘ f ∘ ψ< p)

-- Estimation by ggg community : ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) between ψ(Ω_Ω) and ψ(Ω_(Ω+1))
_ : Ord₀
_ = lim (λ n → ψ₀ (ψ<Ω {n = n} ΩΩ))
