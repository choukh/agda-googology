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
_∈D⟨ω^⟩ : Ord → Type; infix 5 _∈D⟨ω^⟩
ω^ : a ∈D⟨ω^⟩ → Ord

zero ∈D⟨ω^⟩ = ⊤
suc a ∈D⟨ω^⟩ = a ∈D⟨ω^⟩
lim f ∈D⟨ω^⟩ = Σ (∀ n → f n ∈D⟨ω^⟩) λ ḟ → f 0 < ω^ (ḟ 0)
```

```agda
isProp∈D : isProp (a ∈D⟨ω^⟩)
isProp∈D {(zero)} = isProp⊤
isProp∈D {suc a} = isProp∈D {a}
isProp∈D {lim f} = isPropΣ (isPropΠ λ n → isProp∈D {f n}) λ _ → squash₁
```

```agda
ω^-nz : {ȧ : a ∈D⟨ω^⟩} → NonZero (ω^ ȧ)
private instance _ = ω^-nz
```

```agda
ω^-pres-rd : {ȧ : a ∈D⟨ω^⟩} {ḃ : b ∈D⟨ω^⟩} → Road a b → Road (ω^ ȧ) (ω^ ḃ)
ω^-pres< : {ȧ : a ∈D⟨ω^⟩} {ḃ : b ∈D⟨ω^⟩} → a < b → ω^ ȧ < ω^ ḃ
ω^-pres< = map ω^-pres-rd
```

```agda
ω^ {(zero)} tt = 1
ω^ {suc a} ȧ = ω^ ȧ * ω
ω^ {lim f} (ḟ , r) = lim h
  module BaseOmega where
  h : Seq
  h zero = f 0
  h (suc n) = ω^ (ḟ n)
  instance h-wf : wf h
  h-wf {(zero)} = r
  h-wf {suc n} = ω^-pres< it

ω^-nz {a = zero} = _
ω^-nz {a = suc a} = _
ω^-nz {a = lim f} = _

ω^-pres-rd {ȧ} {ḃ} zero = J (λ ċ p → Road (ω^ ȧ) (ω^ ċ * ω)) (set *-infl<) (isProp∈D ȧ ḃ)
ω^-pres-rd {ȧ} {ḃ} (suc r) =  begin-strict
  ω^ ȧ                        <⟨ ω^-pres-rd r ⟩
  ω^ ḃ                        <⟨ set *-infl< ⟩
  ω^ ḃ * ω                    ∎ where open RoadReasoning
ω^-pres-rd {ȧ = ȧ} ḃ@{ḟ , r} (lim {f} {n} s) = begin-strict
  ω^ ȧ                        <⟨ ω^-pres-rd s ⟩
  ω^ (ḟ n)                    <⟨ lim ⦃ h-wf ⦄ (set $ h-wf {suc n}) ⟩
  ω^ ḃ                        ∎ where open RoadReasoning; open BaseOmega f ḟ r
```

```agda
ṅ : ∀ n → fin n ∈D⟨ω^⟩
ṅ zero = tt
ṅ (suc n) = ṅ n
```

```agda
ω^-id : ω^ (ṅ 1) ≡ ω
ω^-id = limExt ⦃ _ ⦄ λ _ → *-idˡ
```

```agda
infix 5 _∈D⟨ω⋰⟩
data _∈D⟨ω⋰⟩ : Ord → Type where
  zero : 0 ∈D⟨ω⋰⟩
  suc : a ∈D⟨ω⋰⟩ → (ȧ : a ∈D⟨ω^⟩) → ω^ ȧ ∈D⟨ω^⟩ → ω^ ȧ ∈D⟨ω⋰⟩
```

```agda
ω⋰ : a ∈D⟨ω⋰⟩ → Ord
ω⋰ zero = lim h ⦃ {!   !} ⦄
  module TowerOmega where
  h : Seq
  ḣ : ∀ n → h n ∈D⟨ω^⟩
  h zero = 0
  h (suc n) = ω^ (ḣ n)
  ḣ 0 {- 0 -}     = tt
  ḣ 1 {- ω^0 -}   = tt
  ḣ 2 {- ω^ω^0 -} = (λ n → subst _∈D⟨ω^⟩ (sym *-idˡ) (ṅ n)) , zero₁
  ḣ (2+ (suc n)) = {! ḣ (2+ n)  !}
ω⋰ (suc ȧ ȧ₁ x) = {!   !}
```
