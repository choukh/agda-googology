```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic

import Cubical.Foundations.Prelude as 🧊
open import Cubical.Foundations.HLevels
```

## 欧米加底运算

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

## 欧米加塔运算

```agda
ω̇ : ω ∈D⟨ω^⟩
ω̇ = ṅ , zero₁

ω^ω : Ord
ω^ω = ω^ {ω} ω̇
```

```agda
_+̇_ : a ∈D⟨ω^⟩ → b ∈D⟨ω^⟩ → a + b ∈D⟨ω^⟩
_+̇_ {b = zero} ȧ tt = ȧ
_+̇_ {b = suc b} ȧ ḃ = ȧ +̇ ḃ
_+̇_ {b = lim f} ȧ (ḟ , r) = (λ n → ȧ +̇ ḟ n) , {!   !}
```

```agda
t : ⦃ nza : NonZero a ⦄ → a ∈D⟨ω^⟩ → (a * fin n) ⦃ nza ⦄ ∈D⟨ω^⟩
t {n = zero} ȧ = tt
t {n = suc zero} ȧ = {!   !}
t {n = 2+ n} ȧ = {!   !}
```

```agda
ω^ṅ : ω^ (ṅ n) ∈D⟨ω^⟩
ω^ṅ {(zero)} = tt
ω^ṅ {suc n} = {!   !} , zero₁

ω^ω̇ : ω^ω ∈D⟨ω^⟩
ω^ω̇ = (λ { zero → tt ; (suc n) → ω^ṅ {n} }) , zero₁
```
