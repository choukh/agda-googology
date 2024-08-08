```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic

import Cubical.Foundations.Prelude as 🧊
open import Cubical.Foundations.HLevels
```

```agda
data _∈D⟨ω^⟩ : Ord → Type; infix 5 _∈D⟨ω^⟩
ω^_ : a ∈D⟨ω^⟩ → Ord

data _∈D⟨ω^⟩ where
  zero : 0 ∈D⟨ω^⟩
  suc  : a ∈D⟨ω^⟩ → suc a ∈D⟨ω^⟩
  lim  : ⦃ _ : wf f ⦄ (ḟ : ∀ n → f n ∈D⟨ω^⟩) (r : f 0 < ω^ ḟ 0) → lim f ∈D⟨ω^⟩
```

```agda
private variable ȧ : a ∈D⟨ω^⟩
ω^-nz : NonZero (ω^ ȧ)
private instance _ = ω^-nz
```

```agda
ω^-pres-rd : {ȧ : a ∈D⟨ω^⟩} {ḃ : b ∈D⟨ω^⟩} → Road a b → Road (ω^ ȧ) (ω^ ḃ)
ω^-pres< : {ȧ : a ∈D⟨ω^⟩} {ḃ : b ∈D⟨ω^⟩} → a < b → ω^ ȧ < ω^ ḃ
ω^-pres< = map ω^-pres-rd
```

```agda
ω^ zero = 1
ω^ (suc ȧ) = ω^ ȧ * ω
ω^ (lim {f} ḟ r) = lim h
  module BaseOmega where
  h : Seq
  h zero = f 0
  h (suc n) = ω^ ḟ n
  instance h-wf : wf h
  h-wf {(zero)} = r
  h-wf {suc n} = ω^-pres< it

ω^-nz {ȧ = zero}    = _
ω^-nz {ȧ = suc ȧ}   = _
ω^-nz {ȧ = lim ḟ r} = _

ω^-pres-rd {ȧ} {suc ḃ} zero = J (λ ċ p → Road (ω^ ȧ) (ω^ ċ * ω))
  (set *-infl<) {!   !}
ω^-pres-rd {ȧ} {suc ḃ} (suc r) = {!   !}
ω^-pres-rd {ȧ} {lim ḟ r} (lim s) = {!   !}
```

```agda
isProp∈D : isProp (a ∈D⟨ω^⟩)
isProp∈D zero zero = 🧊.refl
isProp∈D (suc ȧ) (suc ḃ) = 🧊.cong suc (isProp∈D ȧ ḃ)
isProp∈D (lim {f} ḟ r) (lim ġ s) = 🧊.cong₂ _∈D⟨ω^⟩.lim
  (isPropΠ (λ _ → isProp∈D) _ _) (isProp→PathP (λ _ → squash₁) _ _)
```

```agda
+-∈D : a ∈D⟨ω^⟩ → b ∈D⟨ω^⟩ → a + b ∈D⟨ω^⟩
+-∈D ȧ zero = ȧ
+-∈D ȧ (suc ḃ) = suc (+-∈D ȧ ḃ)
+-∈D ȧ (lim ḟ r) = lim ⦃ +-pres< it ⦄ (λ n → +-∈D ȧ (ḟ n)) {!   !}
```

```agda
ω^-∈D : (ω^ ȧ) ∈D⟨ω^⟩
ω^-∈D {ȧ = zero} = suc zero
ω^-∈D {ȧ = suc ȧ} = lim ⦃ *-pres< it ⦄ ω^*n-∈D nz-elim where
  ω^*n-∈D : ∀ n → ω^ ȧ * fin n ∈D⟨ω^⟩
  ω^*n-∈D zero = zero
  ω^*n-∈D (suc n) = +-∈D (ω^*n-∈D n) ω^-∈D
ω^-∈D {ȧ = lim ḟ r} = lim ⦃ {!   !} ⦄ {!   !} {!   !}
```

```agda
ω⋰ : a ∈D⟨ω^⟩ → Ord
ω⋰ {a} ȧ = lim h ⦃ {!   !} ⦄
  module TowerOmega where
  h : Seq
  h-∈D : h n ∈D⟨ω^⟩
  h zero = a
  h (suc n) = ω^_ {h n} h-∈D
  h-∈D {(zero)} = ȧ
  h-∈D {suc n} = ω^-∈D
```

```agda
ε₀ : Ord
ε₀ = ω⋰ zero
```

```agda
ε̇₀ : ε₀ ∈D⟨ω^⟩
ε̇₀ = lim ⦃ {!   !} ⦄ (λ n → TowerOmega.h-∈D zero) zero₁
```

```agda
ε₀-fix : ω^ ε̇₀ ≡ ε₀
ε₀-fix = limExt ⦃ {!   !} ⦄ ⦃ {!   !} ⦄ (λ { zero → refl ; (suc n) → refl })
```
