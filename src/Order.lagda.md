
```agda
{-# OPTIONS --safe #-}
module Order where
open import Base
```

```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
```

## 前驱

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc α) = ⊤ ⊎ Depth α
Depth (lim f) = Σ[ n ∈ ℕ ] Depth (f n)

private variable d : Depth α
```

```agda
_∸_ : ∀ α → Depth α → Ord; infixl 6 _∸_
suc α ∸ inj₁ tt = α
suc α ∸ inj₂ d  = α ∸ d
lim f ∸ (n , d) = f n ∸ d
```

## 非严格序

```agda
infix 4 _≤_ _<_ _≰_ _≮_
data _≤_ : Ord → Ord → Set
_<_ _≰_ _≮_ : Ord → Ord → Set
α < β = suc α ≤ β
α ≰ β = ¬ α ≤ β
α ≮ β = ¬ α < β

data _≤_ where
  z≤ : zero ≤ β
  s≤ : α ≤ β ∸ d → α < β
  l≤ : (∀ {n} → f n ≤ β) → lim f ≤ β
```

```agda
l≤-inv : lim f ≤ α → f n ≤ α
l≤-inv (l≤ p) = p

l<-inv : lim f < α → f n < α
l<-inv (s≤ p) = s≤ (l≤-inv p)
```

```agda
<→≤ : α < β → α ≤ β
<→≤ (s≤ z≤) = z≤
<→≤ (s≤ (s≤ p)) = s≤ (<→≤ (s≤ p))
<→≤ (s≤ (l≤ p)) = l≤ (<→≤ (s≤ p))
```

```agda
≤l : α ≤ f n → α ≤ lim f
≤l z≤ = z≤
≤l (s≤ p) = s≤ p
≤l (l≤ p) = l≤ (≤l p)

<l : α < f n → α < lim f
<l p = ≤l p
```

```agda
s≤s : α ≤ β → suc α ≤ suc β
s≤s = s≤ {d = inj₁ tt}

z<s : zero < suc α
z<s = s≤s z≤
```

```agda
s≤s-inj : suc α ≤ suc β → α ≤ β
s≤s-inj (s≤ {d = inj₁ tt} p) = p
s≤s-inj (s≤ {d = inj₂ d } p) = <→≤ (s≤ p)
```

```agda
s<s : α < β → suc α < suc β
s<s = s≤s

s<s-inj : suc α < suc β → α < β
s<s-inj = s≤s-inj
```

```agda
l≤l : (∀ {n} → f n ≤ g n) → lim f ≤ lim g
l≤l f≤g = l≤ (≤l f≤g)
```

```agda
≤-refl : α ≤ α
≤-refl {α = zero} = z≤
≤-refl {α = suc α} = s≤s ≤-refl
≤-refl {α = lim x} = l≤l ≤-refl
```

```agda
<s : α < suc α
<s = s≤s ≤-refl

≤s : α ≤ suc α
≤s = <→≤ <s

f≤l : f n ≤ lim f
f≤l = ≤l ≤-refl
```

```agda
≤-trans : α ≤ β → β ≤ γ → α ≤ γ
≤-trans z≤ _ = z≤
≤-trans p@(s≤ _) (s≤ q) = s≤ (≤-trans (s≤s-inj p) q)
≤-trans (s≤ p) (l≤ q) = ≤-trans (s≤ p) q
≤-trans (l≤ p) q = l≤ (≤-trans p q)
```

```agda
s≤→≤ : suc α ≤ β → α ≤ β
s≤→≤ = ≤-trans ≤s

≤→≤s : α ≤ β → α ≤ suc β
≤→≤s p = ≤-trans p ≤s
```

## 外延相等

```agda
_≃_ _≄_ _≢_ : Ord → Ord → Set; infix 4 _≃_ _≄_ _≢_
α ≃ β = α ≤ β × β ≤ α
α ≄ β = ¬ α ≃ β
α ≢ β = ¬ α ≡ β

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
s≃s : α ≃ β → suc α ≃ suc β
s≃s (p , q) = s≤s p , s≤s q

s≃s-inj : suc α ≃ suc β → α ≃ β
s≃s-inj (p , q) = s≤s-inj p , s≤s-inj q
```

```agda
l≃l : (∀ {n} → f n ≃ g n) → lim f ≃ lim g
l≃l f≃g = (l≤l (proj₁ f≃g)) , (l≤l (proj₂ f≃g))
```

## 严格序

```agda
s≰z : suc α ≰ zero
s≰z (s≤ {d = ⊥} ≤) = ⊥

s≰ : suc α ≰ α
s≰ {α = zero} = s≰z
s≰ {α = suc _} p = s≰ (s≤s-inj p)
s≰ {α = lim _} (s≤ (l≤ p)) = s≰ (s≤ p)
```

```agda
<-irrefl : α < β → α ≄ β
<-irrefl p (u , v) = s≰ (≤-trans p v)

<-trans : α < β → β < γ → α < γ
<-trans p q = ≤-trans p (<→≤ q)

<-asym : α < β → β ≮ α
<-asym p q = <-irrefl (<-trans p q) ≃-refl
```

```agda
<→≱ : α < β → β ≰ α
<→≱ p q = <-irrefl (≤-trans p q) ≃-refl

≤⇒≯ : α ≤ β → β ≮ α
≤⇒≯ p q = <-irrefl (≤-trans q p) ≃-refl
```

```agda
<-≤-trans : α < β → β ≤ γ → α ≤ γ
<-≤-trans p q = ≤-trans (<→≤ p) q

≤-<-trans : α ≤ β → β < γ → α ≤ γ
≤-<-trans p q = ≤-trans p (<→≤ q)
```
