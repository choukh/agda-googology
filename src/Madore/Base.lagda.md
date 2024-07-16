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
open import Function public using (id; _∘_; _$_; _∋_; case_of_)
open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality public hiding ([_])

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
  a b c d i : Ord
  f g h : Seq
```

**定义** 良构树序数

```agda
data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : (f : Seq) (f↑ : wf f) → Ord
```

**定义** 子树关系

```agda
data _<_ where
  suc  : a < suc a
  suc₂ : a < b → a < suc b
  lim  : {f↑ : wf f} → f n < lim f f↑
  lim₂ : {f↑ : wf f} → a < f n → a < lim f f↑
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

lim-inj : {f↑ : wf f} {g↑ : wf g} → lim f f↑ ≡ lim g g↑ → f ≡ g
lim-inj refl = refl
```

构造子强化

```agda
lim₂′ : {f↑ : wf f} → a ≤ f n → a < lim f f↑
lim₂′ (inj₁ a<f) = lim₂ a<f
lim₂′ (inj₂ refl) = lim
```

互归纳证明

```agda
z<s : 0 < suc a
z<b : a < b → 0 < b

z<s {a = zero}      = suc
z<s {a = suc a}     = suc₂ z<s
z<s {a = lim f f↑}  = suc₂ (lim₂ {n = 1} (z<b f↑))

z<b suc = z<s
z<b (suc₂ p)        = z<s
z<b (lim {n} {f↑})  = lim₂ {n = suc n} (z<b f↑)
z<b (lim₂ {f↑} _)   = lim₂ {n = 1} (z<b f↑)
```

```agda
z<l : {f↑ : wf f} → 0 < lim f f↑
z<l {f↑} = lim₂ {n = 1} (z<b f↑)
```

```agda
z≤ : 0 ≤ a
z≤ {a = zero}     = inj₂ refl
z≤ {a = suc _}    = inj₁ z<s
z≤ {a = lim _ _}  = inj₁ z<l
```

## 子树关系

```agda
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
```

### 严格偏序

```agda
<-trans : Transitive _<_
<-trans a<b suc = suc₂ a<b
<-trans a<f lim = lim₂ a<f
<-trans a<b (suc₂ b<c) = suc₂ (<-trans a<b b<c)
<-trans a<b (lim₂ b<f) = lim₂ (<-trans a<b b<f)
```

```agda
suc-inv : a < suc b → a ≤ b
suc-inv suc = inj₂ refl
suc-inv (suc₂ a<b) = inj₁ a<b
```

```agda
lim-inv : {f↑ : wf f} → a < lim f f↑ → ∃[ n ] a < f n
lim-inv {f↑} lim   = _ , f↑
lim-inv (lim₂ a<f) = _ , a<f
```

```agda
<-irrefl : Irreflexive _≡_ _<_
<-irrefl {suc a} refl s<s with suc-inv s<s
... | inj₁ s<a = <-irrefl refl (<-trans suc s<a)
<-irrefl {lim f _} refl l<l with lim-inv l<l
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
```

同株不是传递关系.

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
Depth (lim f _) = Σ ℕ λ n → Depth (f n)

private variable δ : Depth a
```

**定义** 前驱运算

```agda
_∸_ : ∀ a → Depth a → Ord; infixl 6 _∸_
suc a   ∸ inj₁ tt = a
suc a   ∸ inj₂ δ  = a ∸ δ
lim f _ ∸ (n , δ) = f n ∸ δ
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
  s≼ : a ≼ b ∸ δ → a ≺ b
  l≼ : {f↑ : wf f} → (∀ {n} → f n ≼ b) → lim f f↑ ≼ b
```

```agda
≺⇒≼ : _≺_ ⇒ _≼_
≺⇒≼ (s≼ z≼) = z≼
≺⇒≼ (s≼ (s≼ p)) = s≼ (≺⇒≼ (s≼ p))
≺⇒≼ (s≼ (l≼ p)) = l≼ (≺⇒≼ (s≼ p))
```

```agda
≼l : {f↑ : wf f} → a ≼ f n → a ≼ lim f f↑
≼l z≼ = z≼
≼l (s≼ p) = s≼ p
≼l (l≼ p) = l≼ (≼l p)

≺l : {f↑ : wf f} → a ≺ f n → a ≺ lim f f↑
≺l p = ≼l p
```

```agda
s≼s : a ≼ b → suc a ≼ suc b
s≼s = s≼ {δ = inj₁ tt}

z≺s : zero ≺ suc a
z≺s = s≼s z≼
```

```agda
s≼s-inj : suc a ≼ suc b → a ≼ b
s≼s-inj (s≼ {δ = inj₁ tt} p) = p
s≼s-inj (s≼ {δ = inj₂ δ } p) = ≺⇒≼ (s≼ p)
```

```agda
s≺s : a ≺ b → suc a ≺ suc b
s≺s = s≼s

s≺s-inj : suc a ≺ suc b → a ≺ b
s≺s-inj = s≼s-inj
```

```agda
l≼l : {f↑ : wf f} {g↑ : wf g}
  → (∀ {n} → f n ≼ g n) → lim f f↑ ≼ lim g g↑
l≼l f≼g = l≼ (≼l f≼g)
```

```agda
≼-refl : a ≼ a
≼-refl {a = zero}     = z≼
≼-refl {a = suc _}    = s≼s ≼-refl
≼-refl {a = lim _ _}  = l≼l ≼-refl
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
≤-monotonic F = ∀ {x y} → x ≤ y → F x ≤ F y

<-monotonic : Func → Set
<-monotonic F = ∀ {x y} → x < y → F x < F y

<-inflationary : Func → Set
<-inflationary F = ∀ {x} → x < F x

≤-inflationary : Func → Set
≤-inflationary F = ∀ {x} → x ≤ F x

normal : <-monotonic F → Set
normal {F} mono = ∀ {f} {f↑ : wf f} → F (lim f f↑) ≡ lim (F ∘̇ f) (mono f↑)
```

```agda
<mono→≤mono : <-monotonic F → ≤-monotonic F
<mono→≤mono <mono (inj₁ p) = <⇒≤ (<mono p)
<mono→≤mono <mono (inj₂ refl) = inj₂ refl
```

后继运算严格单调.

```agda
s<s : <-monotonic suc
suc-trans : a < b → b < c → suc a < c

s<s suc             = suc
s<s (suc₂ x<y)      = suc₂ (s<s x<y)
s<s (lim {f↑})      = suc₂ (lim₂ (suc-trans f↑ f↑))
s<s (lim₂ {f↑} x<f) = suc₂ (lim₂ (suc-trans x<f f↑))

suc-trans a<b suc         = s<s a<b
suc-trans a<b (suc₂ c<b)  = suc₂ (suc-trans a<b c<b)
suc-trans a<f (lim {f↑})  = lim₂ (suc-trans a<f f↑)
suc-trans a<b (lim₂ b<f)  = lim₂ (suc-trans a<b b<f)
```

推论

```agda
s≤s : ≤-monotonic suc
s≤s (inj₁ a<b) = inj₁ (s<s a<b)
s≤s (inj₂ refl) = inj₂ refl
```

```agda
s<s-inj : suc a < suc b → a < b
s<s-inj suc = suc
s<s-inj (suc₂ s<b) = <-trans suc s<b

s≤s-inj : suc a ≤ suc b → a ≤ b
s≤s-inj (inj₁ s<s) = inj₁ (s<s-inj s<s)
s≤s-inj (inj₂ refl) = inj₂ refl
```
