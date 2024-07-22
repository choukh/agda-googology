{-# OPTIONS --safe --lossy-unification #-}

module Madore.Base where

open import Data.Unit public using (⊤)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Function using (id; _∘_; _∋_; it)
open import Relation.Binary.PropositionalEquality public hiding ([_])

data Level : Set
data _⊏_ : Level → Level → Set; infix 4 _⊏_

wfᴸ : (ℕ → Level) → Set
wfᴸ f = ∀ {n} → f n ⊏ f (suc n)

variable
  m n : ℕ
  a b c : Level

data Level where
  zero : Level
  suc  : Level → Level
  lim  : (f : ℕ → Level) → ⦃ wfᴸ f ⦄ → Level

data _⊏_ where
  ⊏suc  : a ⊏ suc a
  ⊏suc₂ : a ⊏ b → a ⊏ suc b
  ⊏lim  : ∀ {f n} {wff : wfᴸ f} → f n ⊏ lim f ⦃ wff ⦄
  ⊏lim₂ : ∀ {f n} {wff : wfᴸ f} → a ⊏ f n → a ⊏ lim f ⦃ wff ⦄

⊏-trans : a ⊏ b → b ⊏ c → a ⊏ c
⊏-trans a⊏b ⊏suc = ⊏suc₂ a⊏b
⊏-trans a⊏f ⊏lim = ⊏lim₂ a⊏f
⊏-trans a⊏b (⊏suc₂ b⊏c) = ⊏suc₂ (⊏-trans a⊏b b⊏c)
⊏-trans a⊏b (⊏lim₂ b⊏f) = ⊏lim₂ (⊏-trans a⊏b b⊏f)

data U (a : Level) (E : ∀ b → b ⊏ a → Set) : Set
data _<_ {a : Level} {E : ∀ b → b ⊏ a → Set} : U a E → U a E → Set; infix 4 _<_

variable
  E : ∀ b → b ⊏ a → Set
  α β γ : U a E

wf : (ℕ → U a E) → Set
wf f = ∀ {n} → f n < f (suc n)

Wf : {⊏a : b ⊏ a} → (E b ⊏a → U a E) → Set
Wf F = ∀ {μ ν} → {!   !} → F μ < F ν

data U a E where
  zero : U a E
  suc  : U a E → U a E
  lim  : (f : ℕ → U a E) → ⦃ wff : wf f ⦄ → U a E
  Limᵖ : (⊏a : b ⊏ a) → (E b ⊏a → U a E) → U a E

data _<_ {a} {E} where
  <suc : α < suc α
  <suc₂ : α < β → α < suc β
  <lim  : ∀ {f n} {wff : wf f} → f n < lim f ⦃ wff ⦄
  <lim₂ : ∀ {f n} {wff : wf f} → α < f n → α < lim f ⦃ wff ⦄
  <Lim  : {⊏a : b ⊏ a} {F : E b ⊏a → U a E} {ν : E b ⊏a} → F ν < Limᵖ ⊏a F
  <Lim₂ : {⊏a : b ⊏ a} {F : E b ⊏a → U a E} {ν : E b ⊏a} → α < F ν → α < Limᵖ ⊏a F

El : ∀ {a} b → b ⊏ a → Set
El b ⊏suc           = U b El
El b (⊏suc₂ ⊏a)     = El b ⊏a
El _ (⊏lim {f} {n}) = U (f n) El
El b (⊏lim₂ ⊏a)     = El b ⊏a

Ord : Level → Set
Ord a = U a El

El≡Ord : (⊏b : a ⊏ b) → El a ⊏b ≡ Ord a
El≡Ord ⊏suc       = refl
El≡Ord (⊏suc₂ ⊏b) = El≡Ord ⊏b
El≡Ord ⊏lim       = refl
El≡Ord (⊏lim₂ ⊏b) = El≡Ord ⊏b

ord : {⊏b : a ⊏ b} → El a ⊏b → Ord a
ord {⊏b} α = subst id (El≡Ord ⊏b) α

el : (⊏b : a ⊏ b) → Ord a → El a ⊏b
el ⊏b α = subst id (sym (El≡Ord ⊏b)) α

el-ord : {⊏b : a ⊏ b} {x : El a ⊏b} → el ⊏b (ord x) ≡ x
el-ord {⊏b} = subst-sym-subst (El≡Ord ⊏b)

Lim : (⊏b : a ⊏ b) → (Ord a → Ord b) → Ord b
Lim ⊏b F = Limᵖ ⊏b (λ α → F (ord α))

open import Lower public using (_∘ⁿ_)
finᴸ : ℕ → Level
finᴸ n = (suc ∘ⁿ n) zero
fin : ℕ → Ord a
fin n = (suc ∘ⁿ n) zero

open import Agda.Builtin.FromNat public
instance
  nNat : Number ℕ
  nNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nLevel : Number Level
  nLevel = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finᴸ n }
  nOrd : Number (Ord a)
  nOrd = record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }

level : Ord 0 → Level
level-pres : α < β → level α ⊏ level β

level zero = zero
level (suc α) = suc (level α)
level (lim f) = lim (λ n → level (f n)) ⦃ level-pres it ⦄

level-pres <suc       = ⊏suc
level-pres (<suc₂ p)  = ⊏suc₂ (level-pres p)
level-pres <lim       = ⊏lim
level-pres (<lim₂ p)  = ⊏lim₂ (level-pres p)

Lift : a ⊏ b → Ord a → Ord b
Lift-pres : {p : a ⊏ b} → α < β → Lift p α < Lift p β

Lift ab zero = zero
Lift ab (suc α) = suc (Lift ab α)
Lift ab (lim f) = lim (Lift ab ∘ f) ⦃ Lift-pres it ⦄
Lift ab (Limᵖ ca F) = Lim (⊏-trans ca ab) λ β → Lift ab (F (el ca β))

Lift-pres <suc = <suc
Lift-pres (<suc₂ p) = <suc₂ (Lift-pres p)
Lift-pres <lim = <lim
Lift-pres (<lim₂ p) = <lim₂ (Lift-pres p)
Lift-pres <Lim = <Lim₂ (Lift-pres {!   !})
Lift-pres (<Lim₂ p) = <Lim₂ (Lift-pres {!   !})

ω : Ord 0
ω = lim fin ⦃ <suc ⦄

Ω : ∀ a → Ord a
Ω-pres : (ac : a ⊏ c) (bc : b ⊏ c) → a ⊏ b → Lift ac (Ω a) < Lift bc (Ω b)

Ω zero = ω
Ω (suc a) = Lim ⊏suc (Lift ⊏suc)
Ω (lim f) = lim (λ n → Lift ⊏lim (Ω (f n))) ⦃ Ω-pres ⊏lim ⊏lim it ⦄

Ω-pres ac bc ⊏suc = <Lim₂ {!   !} -- Lift ac (Ω a) < Lift ac (suc (Ω a)) < Lift bc (Lift ⊏suc (suc (Ω a)))
Ω-pres ac bc (⊏suc₂ p) = {!   !}
Ω-pres ac bc (⊏lim {wff}) = <lim₂ {!   !}
Ω-pres ac bc (⊏lim₂ p) = {!   !}
