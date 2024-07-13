
```agda
{-# OPTIONS --safe --lossy-unification #-}
module WellFormed where
```

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Function using (_∋_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
```

```agda
data Ord : Set
data _<_ : Ord → Ord → Set; infix 4 _<_
pre-suc : Ord → Ord
```

```agda
_≮_ _≤_ _≰_ _≃_ _≄_ _≦_ : Ord → Ord → Set; infix 4 _≮_ _≤_ _≰_ _≃_ _≄_ _≦_
α ≮ β = ¬ α < β
α ≤ β = α < pre-suc β
α ≰ β = ¬ α ≤ β
α ≃ β = α ≤ β × β ≤ α
α ≄ β = ¬ α ≃ β
α ≦ β = α < β ⊎ α ≡ β
```

```agda
isMonoSeq : (ℕ → Ord) → Set
isMonoSeq f = ∀ {n} → f n < f (suc n)

MonoSeq : Set
MonoSeq = Σ (ℕ → Ord) isMonoSeq

_[_] : MonoSeq → ℕ → Ord; infix 30 _[_]
(f , _) [ n ] = f n

mono : ((f , _) : MonoSeq) → isMonoSeq f
mono (_ , fm) = fm
```

```agda
variable
  n : ℕ
  α β γ : Ord
  f : MonoSeq

data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : MonoSeq → Ord
pre-suc = suc
```

```agda
data _<_ where
  ≤-refl : α ≤ α
  <→≤ : α < β → α ≤ β
  f<l : f [ n ] < lim f
  <l : α < f [ n ] → α < lim f
```

```agda
open import Lower public using (_∘ⁿ_)
finord : ℕ → Ord
finord n = (suc ∘ⁿ n) zero

open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord n }
```

```agda
<-trans : α < β → β < γ → α < γ
<-trans p ≤-refl = <→≤ p
<-trans p f<l = <l p
<-trans p (<→≤ q) = <→≤ (<-trans p q)
<-trans p (<l q) = <l (<-trans p q)
```

```agda
<-≤-trans : α < β → β ≤ γ → α ≤ γ
<-≤-trans = <-trans

≤-<-trans : α ≤ β → β < γ → α ≤ γ
≤-<-trans ≤-refl q = <→≤ q
≤-<-trans (<→≤ p) q = <→≤ (<-trans p q)

≤-trans : α ≤ β → β ≤ γ → α ≤ γ
≤-trans ≤-refl q = q
≤-trans (<→≤ p) q = <-trans p q
```

```agda
≤-antisym : α ≤ β → β ≤ α → α ≃ β
≤-antisym = _,_
```

```agda
≃-refl : α ≃ α
≃-refl = ≤-refl , ≤-refl

≃-sym : α ≃ β → β ≃ α
≃-sym (p , q) = q , p

≃-trans : α ≃ β → β ≃ γ → α ≃ γ
≃-trans (p , q) (u , v) = ≤-trans p u , ≤-trans v q
```

```agda
f≢l : f [ n ] ≢ lim f
f≢l {f} {n} p with f [ n ] in eq
f≢l refl | lim g = f≢l eq
```

```agda
<-irrefl-≡ : α < β → α ≢ β
<-irrefl-≡ (<→≤ p) refl = <-irrefl-≡ (<-trans ≤-refl p) refl
<-irrefl-≡ f<l = f≢l
<-irrefl-≡ (<l {f} {n} p) refl with f [ n ] in eq
... | suc _ = <-irrefl-≡ {α = f [ n ]} (<-trans f<l p) eq
... | lim _ = <-irrefl-≡ {α = f [ n ]} (<-trans f<l p) eq
```

```agda
<-irrefl : α ≮ α
<-irrefl p = <-irrefl-≡ p refl

<-asym : α < β → β ≮ α
<-asym p q = <-irrefl (<-trans p q)
```
