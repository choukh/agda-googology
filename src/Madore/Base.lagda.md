---
title: 形式化大数数学 (2.0 - 良构树序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.0 - 良构树序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Madore/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/Madore.Base.html)  

## 前言

```agda
{-# OPTIONS --safe #-}
module Madore.Base where
```

### 标准库依赖

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Function using (id; _∘_; _∋_; it)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
```

## 互归纳定义

互归纳定义良构树序数与子树关系.

```agda
data Ord : Set
data _<_ : Ord → Ord → Set; infix 4 _<_
```

```agda
_≮_ _≤_ _≰_ : Ord → Ord → Set; infix 4 _≮_ _≤_ _≰_
α ≮ β = ¬ α < β
α ≤ β = α < β ⊎ α ≡ β
α ≰ β = ¬ α ≤ β
```

**定义** 单调列

```agda
mono : (ℕ → Ord) → Set
mono f = ∀ {n} → f n < f (suc n)
```

```agda
variable
  n : ℕ
  α β γ : Ord
  f g h : ℕ → Ord
```

**定义** 良构树序数

```agda
data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : (f : ℕ → Ord) → ⦃ mono f ⦄ → Ord
```

**定义** 子树关系

```agda
data _<_ where
  suc  : α < suc α
  suc₂ : α < β → α < suc β
  lim  : ⦃ _ : mono f ⦄ → f n < lim f
  lim₂ : ⦃ _ : mono f ⦄ → α < f n → α < lim f
```

字面量重载

```agda
open import Lower public using (_∘ⁿ_)
finord : ℕ → Ord
finord n = (suc ∘ⁿ n) zero

open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord n }
```

## 子树关系

### 严格偏序

```agda
<-trans : α < β → β < γ → α < γ
<-trans p suc = suc₂ p
<-trans p lim = lim₂ p
<-trans p (suc₂ q) = suc₂ (<-trans p q)
<-trans p (lim₂ q) = lim₂ (<-trans p q)
```

```agda
<l-inv : ⦃ _ : mono f ⦄ → α < lim f → ∃[ n ] α < f n
<l-inv (lim {n}) = suc n , it
<l-inv (lim₂ {n} p) = n , p
```

```agda
<-irrefl : α ≮ α
<-irrefl {α = suc α} (suc₂ p) = <-irrefl {α = α} (<-trans suc p)
<-irrefl {α = lim f} p with <l-inv p
... | n , p = <-irrefl {α = f n} (<-trans lim p)
```

```agda
<-asym : α < β → β ≮ α
<-asym p q = <-irrefl (<-trans p q)
```

### 非严格偏序

```agda
≤-refl : α ≤ α
≤-refl = inj₂ refl

≤-antisym : α ≤ β → β ≤ α → α ≡ β
≤-antisym _ (inj₂ refl) = refl
≤-antisym (inj₂ refl) _ = refl
≤-antisym (inj₁ p) (inj₁ q) = ⊥-elim (<-asym p q)

≤-trans : α ≤ β → β ≤ γ → α ≤ γ
≤-trans (inj₁ p) (inj₁ q) = inj₁ (<-trans p q)
≤-trans p (inj₂ refl) = p
≤-trans (inj₂ refl) q = q
```

### 线序性

```agda
pattern inj² x = inj₂ (inj₁ x)
pattern inj³ x = inj₂ (inj₂ x)
```

```agda
<-dec : α < γ → β < γ → α < β ⊎ α ≡ β ⊎ β < α
<-dec suc       suc       = inj² refl
<-dec suc       (suc₂ q)  = {!   !}
<-dec (suc₂ p)  suc       = {!   !}
<-dec (suc₂ p)  (suc₂ q)  = {!   !}
<-dec lim       lim       = {!   !}
<-dec lim       (lim₂ q)  = {!   !}
<-dec (lim₂ p)  lim       = {!   !}
<-dec (lim₂ p)  (lim₂ q)  = {!   !}
```

**定义** 同株

```agda
_≘_ : Ord → Ord → Set
α ≘ β = ∃[ γ ] (α ≤ γ × β ≤ γ ⊎ γ ≤ α × γ ≤ β)
```

```agda
<-trich : α ≘ β → α < β ⊎ α ≡ β ⊎ β < α
<-trich (γ , inj₁ p) = {!   !}
<-trich (γ , inj₂ q) = {!   !}
```

## 跨树关系

### 前驱

**定义** 前驱深度

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc α) = ⊤ ⊎ Depth α
Depth (lim f) = Σ ℕ λ n → Depth (f n)

private variable d : Depth α
```

**定义** 前驱运算

```agda
_∸_ : ∀ α → Depth α → Ord; infixl 6 _∸_
suc α ∸ inj₁ tt = α
suc α ∸ inj₂ d  = α ∸ d
lim f ∸ (n , d) = f n ∸ d
```

### 非严格偏序

```agda
infix 4 _≼_ _≺_ _⋠_ _⊀_
data _≼_ : Ord → Ord → Set
_≺_ _⋠_ _⊀_ : Ord → Ord → Set
α ≺ β = suc α ≼ β
α ⋠ β = ¬ α ≼ β
α ⊀ β = ¬ α ≺ β

data _≼_ where
  z≼ : zero ≼ β
  s≼ : α ≼ β ∸ d → α ≺ β
  l≼ : ⦃ _ : mono f ⦄ → (∀ {n} → f n ≼ β) → lim f ≼ β
```

```agda
≺→≼ : α ≺ β → α ≼ β
≺→≼ (s≼ z≼) = z≼
≺→≼ (s≼ (s≼ p)) = s≼ (≺→≼ (s≼ p))
≺→≼ (s≼ (l≼ p)) = l≼ (≺→≼ (s≼ p))
```

```agda
module _ ⦃ _ : mono f ⦄ where
```

```agda
  ≼l : α ≼ f n → α ≼ lim f
  ≼l z≼ = z≼
  ≼l (s≼ p) = s≼ p
  ≼l (l≼ p) = l≼ (≼l p)

  ≺l : α ≺ f n → α ≺ lim f
  ≺l p = ≼l p
```

```agda
s≼s : α ≼ β → suc α ≼ suc β
s≼s = s≼ {d = inj₁ tt}

z≺s : zero ≺ suc α
z≺s = s≼s z≼
```

```agda
s≼s-inj : suc α ≼ suc β → α ≼ β
s≼s-inj (s≼ {d = inj₁ tt} p) = p
s≼s-inj (s≼ {d = inj₂ d } p) = ≺→≼ (s≼ p)
```

```agda
s≺s : α ≺ β → suc α ≺ suc β
s≺s = s≼s

s≺s-inj : suc α ≺ suc β → α ≺ β
s≺s-inj = s≼s-inj
```

```agda
l≼l : ⦃ _ : mono f ⦄ ⦃ _ : mono g ⦄
  → (∀ {n} → f n ≼ g n) → lim f ≼ lim g
l≼l f≼g = l≼ (≼l f≼g)
```

```agda
≼-refl : α ≼ α
≼-refl {α = zero} = z≼
≼-refl {α = suc _} = s≼s ≼-refl
≼-refl {α = lim _} = l≼l ≼-refl
```

### 外延相等

### 严格偏序
