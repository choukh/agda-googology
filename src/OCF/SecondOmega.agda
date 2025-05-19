{-# OPTIONS --safe --lossy-unification #-}

module OCF.SecondOmega where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)

transport : {A B : Set} → A ≡ B → A → B
transport refl x = x

module ℕ where
  open import Data.Nat using (ℕ; zero; suc) public
  variable n m : ℕ

  iter : {T : Set} (f : T → T) (init : T) (times : ℕ) → T
  iter f a zero    = a
  iter f a (suc n) = f (iter f a n)

  data _<_ : ℕ → ℕ → Set where
    zero : n < suc n
    suc  : n < m → n < suc m

  z<s : ∀ n → zero < suc n
  z<s zero    = zero
  z<s (suc n) = suc (z<s n)

  s<s : n < m → suc n < suc m
  s<s zero      = zero
  s<s (suc p)  = suc (s<s p)

  <-dec : ∀ n m → n < m ⊎ m < n ⊎ n ≡ m
  <-dec zero zero = injᶜ refl
  <-dec zero (suc b) = injᵃ (z<s b)
  <-dec (suc a) zero = injᵇ (z<s a)
  <-dec (suc a) (suc b) with <-dec a b
  ... | injᵃ p = injᵃ (s<s p)
  ... | injᵇ p = injᵇ (s<s p)
  ... | injᶜ p = injᶜ (cong suc p)

open ℕ using (ℕ; zero; suc) renaming (_<_ to _<₀_)

module Ω₁ where
  data Ω₁ : Set
  data _<_ : Ω₁ → Ω₁ → Set

  monotonic : (ℕ → Ω₁) → Set
  monotonic f = ∀ {n m} → n <₀ m → f n < f m

  private variable
    a b c : Ω₁
    f :  ℕ → Ω₁
    mono : monotonic f

  data Ω₁ where
    zero : Ω₁
    suc  : Ω₁ → Ω₁
    lim  : (f : ℕ → Ω₁) (mono : monotonic f) → Ω₁

  data _<_ where
    zero : a < suc a
    suc  : a < b → a < suc b
    lim  : ∀ n → a < f n → a < lim f mono

  f<l : ∀ n → f n < lim f mono
  f<l {mono} n = lim (suc n) (mono zero)

  ↑ : ℕ → Ω₁
  ↑ zero = zero
  ↑ (suc n) = suc (↑ n)

  ↑-mono : monotonic ↑
  ↑-mono zero = zero
  ↑-mono (suc p) = suc (↑-mono p)

  ω : Ω₁
  ω = lim ↑ ↑-mono

  <-trans : a < b → b < c → a < c
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
  <-trans p (lim n q) = lim n (<-trans p q)

  <-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b
  <-dec zero zero       = injᶜ refl
  <-dec zero (suc q)    = injᵇ q
  <-dec (suc p) zero    = injᵃ p
  <-dec (suc p) (suc q) = <-dec p q
  <-dec (lim {mono} n p) (lim m q) with ℕ.<-dec n m
  ... | injᵃ n<m  = <-dec (<-trans p (mono n<m)) q
  ... | injᵇ m<n  = <-dec p (<-trans q (mono m<n))
  ... | injᶜ refl = <-dec p q

open Ω₁ using (Ω₁; zero; suc; lim) renaming (_<_ to _<₁_)

module Ω₂ where
  data Ω₂ : Set
  data _<_ : Ω₂ → Ω₂ → Set

  monotonic : (ℕ → Ω₂) → Set
  monotonic f = ∀ {n m} → n <₀ m → f n < f m

  Monotonic : (Ω₁ → Ω₂) → Set
  Monotonic F = ∀ {a b} → a <₁ b → F a < F b

  private variable
    a b c : Ω₂
    f : ℕ → Ω₂
    F : Ω₁ → Ω₂
    mono : monotonic f
    Mono : Monotonic F

  data Ω₂ where
    zero  : Ω₂
    suc   : Ω₂ → Ω₂
    lim   : (f : ℕ → Ω₂) (mono : monotonic f) → Ω₂
    Lim   : (F : Ω₁ → Ω₂) (Mono : Monotonic F) → Ω₂

  data _<_ where
    zero : a < suc a
    suc  : a < b → a < suc b
    lim  : ∀ n → a < f n → a < lim f mono
    Lim  : ∀ α → a < F α → a < Lim F Mono

  f<l : ∀ n → f n < lim f mono
  f<l {mono} n = lim (suc n) (mono zero)

  F<L : ∀ α → F α < Lim F Mono
  F<L {Mono} α = Lim (suc α) (Mono zero)

  ↑ : ℕ → Ω₂
  ↑ zero = zero
  ↑ (suc n) = suc (↑ n)

  ↑-mono : monotonic ↑
  ↑-mono zero = zero
  ↑-mono (suc p) = suc (↑-mono p)

  ω : Ω₂
  ω = lim ↑ ↑-mono

  mutual
    ⇑ : Ω₁ → Ω₂
    ⇑ zero = zero
    ⇑ (suc α) = suc (⇑ α)
    ⇑ (lim f mono) = lim (⇑ ∘ f) (⇑-mono ∘ mono)

    ⇑-mono : Monotonic ⇑
    ⇑-mono zero = zero
    ⇑-mono (suc p) = suc (⇑-mono p)
    ⇑-mono (lim n p) = lim n (⇑-mono p)

  ω₁ : Ω₂
  ω₁ = Lim ⇑ ⇑-mono

  <-trans : a < b → b < c → a < c
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
  <-trans p (lim n q) = lim n (<-trans p q)
  <-trans p (Lim α q) = Lim α (<-trans p q)

  <-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b
  <-dec zero zero       = injᶜ refl
  <-dec zero (suc q)    = injᵇ q
  <-dec (suc p) zero    = injᵃ p
  <-dec (suc p) (suc q) = <-dec p q
  <-dec (lim {mono} n p) (lim m q) with ℕ.<-dec n m
  ... | injᵃ n<m  = <-dec (<-trans p (mono n<m)) q
  ... | injᵇ m<n  = <-dec p (<-trans q (mono m<n))
  ... | injᶜ refl = <-dec p q
  <-dec (Lim {Mono} α p) (Lim β q) = {!   !}
