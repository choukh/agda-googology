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
open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤; tt)
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Product public using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Function public using (id; _∘_; _∋_; it)
open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; refl; sym)

open import Relation.Binary
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
```

## 互归纳定义

互归纳定义良构树序数与子树关系.

```agda
data Ord : Set
data _<_ : Ord → Ord → Set; infix 4 _<_
```

```agda
open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as SubTreeLe public using (_≤_; <⇒≤)
```

**定义** 递增序列

```agda
Seq : Set
Seq = ℕ → Ord

wf : Seq → Set
wf f = ∀ {n} → f n < f (suc n)
```

```agda
variable
  n : ℕ
  α β γ ι : Ord
  f g h : Seq
```

**定义** 良构树序数

```agda
data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : (f : Seq) → ⦃ wf f ⦄ → Ord
```

**定义** 子树关系

```agda
data _<_ where
  suc  : α < suc α
  suc₂ : α < β → α < suc β
  lim  : ⦃ _ : wf f ⦄ → f n < lim f
  lim₂ : ⦃ _ : wf f ⦄ → α < f n → α < lim f
```

构造子性质

```agda
suc-inj : suc α ≡ suc β → α ≡ β
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

```agda
suc-inv : α < suc β → α ≤ β
suc-inv suc = inj₂ refl
suc-inv (suc₂ α<β) = inj₁ α<β
```

```agda
lim-inv : ⦃ _ : wf f ⦄ → α < lim f → ∃[ n ] α < f n
lim-inv (lim {n}) = suc n , it
lim-inv (lim₂ {n} α<f) = n , α<f
```

字面量重载

```agda
open import Lower public using (_∘ⁿ_)
fin : Seq
fin n = (suc ∘ⁿ n) zero

open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }
```

## 子树关系

```agda
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
```

### 严格偏序

```agda
<-trans : Transitive _<_
<-trans α<β suc = suc₂ α<β
<-trans α<f lim = lim₂ α<f
<-trans p (suc₂ q) = suc₂ (<-trans p q)
<-trans p (lim₂ q) = lim₂ (<-trans p q)
```

```agda
<-irrefl : Irreflexive _≡_ _<_
<-irrefl {suc α} refl q with suc-inv q
... | inj₁ q = <-irrefl refl (<-trans suc q)
<-irrefl {lim f} refl q with lim-inv q
... | n , q = <-irrefl refl (<-trans lim q)
```

```agda
<-asym : Asymmetric _<_
<-asym = trans∧irr⇒asym {_≈_ = _≡_} refl <-trans <-irrefl
```

```agda
<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

```agda
<-isStrictPartialOrder : ≡.IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = <-irrefl
  ; trans = <-trans
  ; <-resp-≈ = <-resp-≡ }
```

### 非严格偏序

```agda
≤-refl : Reflexive _≤_
≤-refl = SubTreeLe.reflexive refl

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = SubTreeLe.antisym isEquivalence <-trans <-irrefl

≤-trans : Transitive _≤_
≤-trans = SubTreeLe.trans isEquivalence <-resp-≡ <-trans
```

```agda
<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans = SubTreeLe.<-≤-trans <-trans (proj₁ <-resp-≡)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans = SubTreeLe.≤-<-trans sym <-trans (proj₂ <-resp-≡)
```

```agda
≤-isPreorder : ≡.IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inj₂
  ; trans = ≤-trans
  }

≤-isPartialOrder : ≡.IsPartialOrder _≤_
≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }
```

```agda
module SubTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
    ≤-isPreorder <-asym <-trans <-resp-≡ <⇒≤ <-≤-trans
    public
```

### 受限的三歧性

```agda
pattern inj² x = inj₂ (inj₁ x)
pattern inj³ x = inj₂ (inj₂ x)
```

```agda
<-trich : α < γ → β < γ → α < β ⊎ α ≡ β ⊎ β < α
<-trich suc       suc       = inj² refl
<-trich suc       (suc₂ q)  = inj³ q
<-trich (suc₂ p)  suc       = inj₁ p
<-trich (suc₂ p)  (suc₂ q)  = <-trich p q
<-trich lim       lim       = {!   !}
<-trich lim       (lim₂ q)  = {!   !}
<-trich (lim₂ p)  lim       = {!   !}
<-trich (lim₂ p)  (lim₂ q)  = {!   !}
```

**定义** 同株

```agda
_≘_ : Ord → Ord → Set
α ≘ β = ∃[ γ ] α ≤ γ × β ≤ γ
```

```agda
<-trich-≘ : α ≘ β → α < β ⊎ α ≡ β ⊎ β < α
<-trich-≘ (γ , inj₁ p , inj₁ q) = <-trich p q
<-trich-≘ (γ , inj₁ p , inj₂ refl) = inj₁ p
<-trich-≘ (γ , inj₂ refl , inj₁ q) = inj³ q
<-trich-≘ (γ , inj₂ refl , inj₂ q) = inj² (sym q)

≤-total-≘ : α ≘ β → α ≤ β ⊎ β ≤ α
≤-total-≘ p with <-trich-≘ p
... | inj₁ p = inj₁ (inj₁ p)
... | inj² p = inj₁ (inj₂ p)
... | inj³ p = inj₂ (inj₁ p)
```

```agda
≘-refl : α ≘ α
≘-refl = _ , ≤-refl , ≤-refl
```

```agda
≘-sym : α ≘ β → β ≘ α
≘-sym (γ , p , q) = γ , q , p
```

```agda
≘-trans : α ≘ β → β ≘ γ → α ≘ γ
≘-trans p q = {!   !}
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

```agda
infix 4 _≼_ _⋠_ _≺_ _⊀_ _≃_ _≄_
data _≼_ : Ord → Ord → Set
_⋠_ _≺_ _⊀_ _≃_ _≄_ : Ord → Ord → Set
α ⋠ β = ¬ α ≼ β
α ≺ β = suc α ≼ β
α ⊀ β = ¬ α ≺ β
α ≃ β = α ≼ β × β ≼ α
α ≄ β = ¬ α ≃ β
```

### 非严格偏序

```agda
data _≼_ where
  z≼ : zero ≼ β
  s≼ : α ≼ β ∸ d → α ≺ β
  l≼ : ⦃ _ : wf f ⦄ → (∀ {n} → f n ≼ β) → lim f ≼ β
```

```agda
≺⇒≼ : _≺_ ⇒ _≼_
≺⇒≼ (s≼ z≼) = z≼
≺⇒≼ (s≼ (s≼ p)) = s≼ (≺⇒≼ (s≼ p))
≺⇒≼ (s≼ (l≼ p)) = l≼ (≺⇒≼ (s≼ p))
```

```agda
module _ ⦃ _ : wf f ⦄ where
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
s≼s-inj (s≼ {d = inj₂ d } p) = ≺⇒≼ (s≼ p)
```

```agda
s≺s : α ≺ β → suc α ≺ suc β
s≺s = s≼s

s≺s-inj : suc α ≺ suc β → α ≺ β
s≺s-inj = s≼s-inj
```

```agda
l≼l : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄
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

## 序数函数

```agda
Func : Set
Func = Ord → Ord
variable F : Func

_∘̇_ : Func → Seq → Seq
F ∘̇ f = λ n → F (f n)
```

```agda
≤-monotonic : Func → Set
≤-monotonic F = ∀ {α β} → α ≤ β → F α ≤ F β

<-monotonic : Func → Set
<-monotonic F = ∀ {α β} → α < β → F α < F β

<-inflationary : Func → Set
<-inflationary F = ∀ {α} → α < F α

≤-inflationary : Func → Set
≤-inflationary F = ∀ {α} → α ≤ F α

normal : <-monotonic F → Set
normal {F} mono = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘̇ f) ⦃ mono it ⦄
```

```agda
<-mono→≤-mono : <-monotonic F → ≤-monotonic F
<-mono→≤-mono <-mono (inj₁ p) = <⇒≤ (<-mono p)
<-mono→≤-mono <-mono (inj₂ refl) = inj₂ refl
```
