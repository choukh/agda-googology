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
open import Data.Nat as ℕ public using (ℕ; zero; suc)
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
  a b c i : Ord
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
  suc  : a < suc a
  suc₂ : a < b → a < suc b
  lim  : ⦃ _ : wf f ⦄ → f n < lim f
  lim₂ : ⦃ _ : wf f ⦄ → a < f n → a < lim f
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

```agda
pattern 2+ a = suc (suc a)
```

## 基本性质

构造子性质

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

$<$ 的传递性

```agda
<-trans : Transitive _<_
<-trans a<b suc = suc₂ a<b
<-trans a<f lim = lim₂ a<f
<-trans a<b (suc₂ b<c) = suc₂ (<-trans a<b b<c)
<-trans a<b (lim₂ b<f) = lim₂ (<-trans a<b b<f)
```

互归纳证明

```agda
z<s : zero < suc a
z<b : a < b → zero < b

z<s {a = zero}  = suc
z<s {a = suc a} = suc₂ z<s
z<s {a = lim f} = suc₂ (lim₂ {n = 1} (z<b it))

z<b suc = z<s
z<b (suc₂ p) = z<s
z<b (lim {n}) = lim₂ {n = suc n} (z<b it)
z<b (lim₂ p) = lim₂ {n = 1} (z<b it)
```

```agda
z<l : ⦃ _ : wf f ⦄ → zero < lim f
z<l = lim₂ {n = 1} (z<b it)
```

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
≤-monotonic F = ∀ {a b} → a ≤ b → F a ≤ F b

<-monotonic : Func → Set
<-monotonic F = ∀ {a b} → a < b → F a < F b

<-inflationary : Func → Set
<-inflationary F = ∀ {a} → a < F a

≤-inflationary : Func → Set
≤-inflationary F = ∀ {a} → a ≤ F a

normal : <-monotonic F → Set
normal {F} mono = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘̇ f) ⦃ mono it ⦄
```

```agda
<mono→≤mono : <-monotonic F → ≤-monotonic F
<mono→≤mono <mono (inj₁ p) = <⇒≤ (<mono p)
<mono→≤mono <mono (inj₂ refl) = inj₂ refl
```

```agda
s<s : <-monotonic suc
suc-trans : a < b → b < c → suc a < c

s<s suc = suc
s<s (suc₂ p) = suc₂ (s<s p)
s<s lim = suc₂ (lim₂ (suc-trans it it))
s<s (lim₂ p) = suc₂ (lim₂ (suc-trans p it))

suc-trans p suc = s<s p
suc-trans p (suc₂ q) = suc₂ (suc-trans p q)
suc-trans p lim = lim₂ (suc-trans p it)
suc-trans p (lim₂ q) = lim₂ (suc-trans p q)
```

```agda
s<s-inj : suc a < suc b → a < b
s<s-inj suc = suc
s<s-inj (suc₂ p) = <-trans suc p
```

```agda
s≤s : ≤-monotonic suc
s≤s (inj₁ a<b) = inj₁ (s<s a<b)
s≤s (inj₂ refl) = inj₂ refl

s≤s-inj : suc a ≤ suc b → a ≤ b
s≤s-inj (inj₁ s<s) = inj₁ (s<s-inj s<s)
s≤s-inj (inj₂ refl) = inj₂ refl
```

序数函数必须互递归定义.

```agda
sup : Ord → Ord → Ord
sup≥₂ : a ≤ sup b a
sup-< : <-monotonic (λ a → sup a c)

sup zero    a@_     = a
sup a@_     zero    = a
sup (suc a) (suc b) = suc (sup a b)
sup a@_     (lim f) = lim (λ n → sup (f n) a) ⦃ sup-< it ⦄
sup (lim f) a@_     = lim (λ n → sup (f n) a) ⦃ sup-< it ⦄

sup≥₂ {a = zero}  {b = zero}  = inj₂ refl
sup≥₂ {a = suc a} {b = zero}  = inj₂ refl
sup≥₂ {a = lim f} {b = zero}  = inj₂ refl
sup≥₂ {a = zero}  {b = suc b} = inj₁ z<s
sup≥₂ {a = suc a} {b = suc b} = s≤s (sup≥₂ {a} {b})
sup≥₂ {a = zero}  {b = lim g} = inj₁ z<l
sup≥₂ {a = suc a} {b = lim g} = {!   !}
sup≥₂ {a = lim f} {b = suc b} = {!   !}
sup≥₂ {a = lim f} {b = lim g} = {!   !}

sup-< {c = zero}  {a = zero}  {b = suc b} p = z<s
sup-< {c = zero}  {a = suc a} {b = suc b} p = p
sup-< {c = zero}  {a = lim f} {b = suc b} p = p
sup-< {c = suc c} {a = zero}  {b = suc b} p = {!   !}
sup-< {c = suc c} {a = suc a} {b = suc b} p = s<s (sup-< (s<s-inj p))
sup-< {c = suc c} {a = lim f} {b = suc b} p = {!   !}
sup-< {c = lim h} {a = a}     {b = suc b} p = {!   !}
sup-< {c = c}     {a = a}     {b = lim g} p = {!   !}
```

## 子树关系

```agda
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
```

### 严格偏序

```agda
suc-inv : a < suc b → a ≤ b
suc-inv suc = inj₂ refl
suc-inv (suc₂ a<b) = inj₁ a<b
```

```agda
lim-inv : ⦃ _ : wf f ⦄ → a < lim f → ∃[ n ] a < f n
lim-inv (lim {n}) = suc n , it
lim-inv (lim₂ {n} a<f) = n , a<f
```

```agda
<-irrefl : Irreflexive _≡_ _<_
<-irrefl {suc a} refl s<s with suc-inv s<s
... | inj₁ s<a = <-irrefl refl (<-trans suc s<a)
<-irrefl {lim f} refl l<l with lim-inv l<l
... | n , l<f = <-irrefl refl (<-trans lim l<f)
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

### 不完全的三歧性

```agda
pattern inj² x = inj₂ (inj₁ x)
pattern inj³ x = inj₂ (inj₂ x)
```

```agda
<-trich : a < c → b < c → a < b ⊎ a ≡ b ⊎ b < a
<-trich suc         suc         = inj² refl
<-trich suc         (suc₂ b<a)  = inj³ b<a
<-trich (suc₂ a<b)  suc         = inj₁ a<b
<-trich (suc₂ a<c)  (suc₂ b<c)  = <-trich a<c b<c
<-trich lim         lim         = {!   !}
<-trich lim         (lim₂ b<f)  = {!   !}
<-trich (lim₂ a<f)  lim         = {!   !}
<-trich (lim₂ a<f)  (lim₂ b<f)  = {!   !}
```

**定义** 同株

```agda
_≘_ : Ord → Ord → Set
a ≘ b = ∃[ c ] a ≤ c × b ≤ c
```

```agda
≘-refl : a ≘ a
≘-refl = _ , ≤-refl , ≤-refl

≘-sym : a ≘ b → b ≘ a
≘-sym (c , a≤c , b≤c) = c , b≤c , a≤c

≘-trans : a ≘ b → b ≘ c → a ≘ c
≘-trans p q = {!   !}
```

```agda
<-trich-≘ : a ≘ b → a < b ⊎ a ≡ b ⊎ b < a
<-trich-≘ (c , inj₁ p , inj₁ q) = <-trich p q
<-trich-≘ (c , inj₁ p , inj₂ refl) = inj₁ p
<-trich-≘ (c , inj₂ refl , inj₁ q) = inj³ q
<-trich-≘ (c , inj₂ refl , inj₂ q) = inj² (sym q)

≤-total-≘ : a ≘ b → a ≤ b ⊎ b ≤ a
≤-total-≘ p with <-trich-≘ p
... | inj₁ p = inj₁ (inj₁ p)
... | inj² p = inj₁ (inj₂ p)
... | inj³ p = inj₂ (inj₁ p)
```

## 跨树关系

### 前驱

**定义** 前驱深度

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc a) = ⊤ ⊎ Depth a
Depth (lim f) = Σ ℕ λ n → Depth (f n)

private variable d : Depth a
```

**定义** 前驱运算

```agda
_∸_ : ∀ a → Depth a → Ord; infixl 6 _∸_
suc a ∸ inj₁ tt = a
suc a ∸ inj₂ d  = a ∸ d
lim f ∸ (n , d) = f n ∸ d
```

```agda
infix 4 _≼_ _⋠_ _≺_ _⊀_ _≃_ _≄_
data _≼_ : Ord → Ord → Set
_⋠_ _≺_ _⊀_ _≃_ _≄_ : Ord → Ord → Set
a ⋠ b = ¬ a ≼ b
a ≺ b = suc a ≼ b
a ⊀ b = ¬ a ≺ b
a ≃ b = a ≼ b × b ≼ a
a ≄ b = ¬ a ≃ b
```

### 非严格偏序

```agda
data _≼_ where
  z≼ : zero ≼ b
  s≼ : a ≼ b ∸ d → a ≺ b
  l≼ : ⦃ _ : wf f ⦄ → (∀ {n} → f n ≼ b) → lim f ≼ b
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
  ≼l : a ≼ f n → a ≼ lim f
  ≼l z≼ = z≼
  ≼l (s≼ p) = s≼ p
  ≼l (l≼ p) = l≼ (≼l p)

  ≺l : a ≺ f n → a ≺ lim f
  ≺l p = ≼l p
```

```agda
s≼s : a ≼ b → suc a ≼ suc b
s≼s = s≼ {d = inj₁ tt}

z≺s : zero ≺ suc a
z≺s = s≼s z≼
```

```agda
s≼s-inj : suc a ≼ suc b → a ≼ b
s≼s-inj (s≼ {d = inj₁ tt} p) = p
s≼s-inj (s≼ {d = inj₂ d } p) = ≺⇒≼ (s≼ p)
```

```agda
s≺s : a ≺ b → suc a ≺ suc b
s≺s = s≼s

s≺s-inj : suc a ≺ suc b → a ≺ b
s≺s-inj = s≼s-inj
```

```agda
l≼l : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄
  → (∀ {n} → f n ≼ g n) → lim f ≼ lim g
l≼l f≼g = l≼ (≼l f≼g)
```

```agda
≼-refl : a ≼ a
≼-refl {a = zero} = z≼
≼-refl {a = suc _} = s≼s ≼-refl
≼-refl {a = lim _} = l≼l ≼-refl
```

### 外延相等
 
### 严格偏序
 