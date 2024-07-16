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
  lim  : (f : Seq) → wf f → Ord
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
normal {F} mono = ∀ {f} {f↑ : wf f} → F (lim f f↑) ≡ lim (F ∘̇ f) (mono f↑)
```

```agda
<mono→≤mono : <-monotonic F → ≤-monotonic F
<mono→≤mono <mono (inj₁ p) = <⇒≤ (<mono p)
<mono→≤mono <mono (inj₂ refl) = inj₂ refl
```

序数函数必须互递归定义.

```agda
module Pre where
  _+_ : Ord → Ord → Ord; infixl 6 _+_
  +-<monoʳ : ∀ c → <-monotonic (c +_)

  zero + b = b
  a + zero      = a
  a + suc b     = suc (a + b)
  a + lim f f↑ = lim (λ n → a + f n) (+-<monoʳ a f↑)

  +-<monoʳ zero = id
  +-<monoʳ (suc c)    suc         = suc
  +-<monoʳ (suc c)    (suc₂ a<b)  = suc₂ (+-<monoʳ (suc c) a<b)
  +-<monoʳ (suc c)    lim         = lim
  +-<monoʳ (suc c)    (lim₂ a<f)  = lim₂ (+-<monoʳ (suc c) a<f)
  +-<monoʳ (lim f f↑) suc         = suc
  +-<monoʳ (lim f f↑) (suc₂ a<b)  = suc₂ (+-<monoʳ (lim f f↑) a<b)
  +-<monoʳ (lim f f↑) lim         = lim
  +-<monoʳ (lim f f↑) (lim₂ a<f)  = lim₂ (+-<monoʳ (lim f f↑) a<f)
```

```agda
  +-≤inflʳ : ∀ a → ≤-inflationary (a +_)
  +-≤inflʳ = {!   !}
```

```agda
  +-≤inflˡ : ∀ b → ≤-inflationary (_+ b)
  +-≤inflˡ b            {(zero)}      = z≤
  +-≤inflˡ zero         {suc _}       = inj₂ refl
  +-≤inflˡ (suc b)      a@{suc _}     = inj₁ $ case (+-≤inflˡ b {a}) of λ
    { (inj₁ a<a+b) → suc₂ a<a+b
    ; (inj₂ a≡a+b) → subst (_< suc (a + b)) (sym a≡a+b) suc }
  +-≤inflˡ b@(lim g _)  a@{suc _}     = inj₁ $ case (+-≤inflˡ (g 0) {a}) of λ
    { (inj₁ a<a+g) → lim₂ a<a+g
    ; (inj₂ a≡a+g) → subst (_< a + b) (sym a≡a+g) lim }
  +-≤inflˡ zero         a@{lim _ _}   = inj₂ refl
  +-≤inflˡ (suc b)      a@{lim f _}   = inj₁ $ case (+-≤inflˡ b {a}) of λ
    { (inj₁ l<l+b) → suc₂ l<l+b
    ; (inj₂ l≡l+b) → subst (_< suc (a + b)) (sym l≡l+b) suc }
  +-≤inflˡ b@(lim g _)  a@{lim f _}   = inj₁ $ case +-≤inflˡ (g 0) {a} of λ
    { (inj₁ l<l+g) → lim₂ l<l+g
    ; (inj₂ l≡l+g) → subst (_< (a + b)) (sym l≡l+g) lim }
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

≘-trans : a ≘ b → b ≘ c → a ≘ c
≘-trans {a} {b} (d , a≤d , _) (e , _ , c≤e) = d Pre.+ e ,
  ≤-trans a≤d (Pre.+-≤inflˡ e) ,
  ≤-trans c≤e (Pre.+-≤inflʳ d)
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

### 单射性

```agda
s<s : <-monotonic suc
suc-trans : a < b → b < c → suc a < c

s<s suc = suc
s<s (suc₂ p) = suc₂ (s<s p)
s<s (lim {f↑}) = suc₂ (lim₂ (suc-trans f↑ f↑))
s<s (lim₂ {f↑} p) = suc₂ (lim₂ (suc-trans p f↑))

suc-trans p suc = s<s p
suc-trans p (suc₂ q) = suc₂ (suc-trans p q)
suc-trans p (lim {f↑}) = lim₂ (suc-trans p f↑)
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
