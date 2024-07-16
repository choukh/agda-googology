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
{-# OPTIONS --safe --lossy-unification #-}
module Madore.Base where
```

### 标准库依赖

```agda
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ public using ()
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Product public using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Function public using (id; _∘_; _$_; _∋_; it)
open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Relation.Binary
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
```

## 良构树序数

互归纳定义良构树序数与子树关系.

```agda
data Ord : Set
data _<_ : Ord → Ord → Set; infix 4 _<_
```

```agda
open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as SubTreeLe public using (_≤_; <⇒≤)
```

**定义** 良构序列

```agda
Seq : Set
Seq = ℕ → Ord

wf : Seq → Set
wf f = ∀ {n} → f n < f (suc n)
```

```agda
variable
  m n : ℕ
  a b c d i : Ord
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

```agda
lim≤ : ⦃ _ : wf f ⦄ → a ≤ f n → a < lim f
lim≤ (inj₁ a<f) = lim₂ a<f
lim≤ (inj₂ refl) = lim
```

互归纳证明

```agda
z<s : 0 < suc a
z<b : a < b → 0 < b

z<s {a = zero}  = suc
z<s {a = suc _} = suc₂ z<s
z<s {a = lim _} = suc₂ (lim₂ {n = 1} (z<b it))

z<b suc = z<s
z<b (suc₂ _)  = z<s
z<b (lim {n}) = lim₂ {n = suc n} (z<b it)
z<b (lim₂ _)  = lim₂ {n = 1} (z<b it)
```

```agda
z<l : ⦃ _ : wf f ⦄ → 0 < lim f
z<l = lim₂ {n = 1} (z<b it)
```

```agda
z≤ : 0 ≤ a
z≤ {a = zero}   = inj₂ refl
z≤ {a = suc _}  = inj₁ z<s
z≤ {a = lim _}  = inj₁ z<l
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
lim-inv : ⦃ _ : wf f ⦄ → a < lim f → ∃[ n ] a < f n
lim-inv lim   = _ , it
lim-inv (lim₂ a<f) = _ , a<f
```

```agda
<-irrefl : Irreflexive _≡_ _<_
<-irrefl {suc a} refl s<s with suc-inv s<s
... | inj₁ s<a = <-irrefl refl (<-trans suc s<a)
<-irrefl {lim _} refl l<l with lim-inv l<l
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
open import Relation.Binary.Reasoning.Base.Triple
  {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
  ≤-isPreorder <-asym <-trans <-resp-≡ <⇒≤ <-≤-trans ≤-<-trans
  public
```

### 不完全的三歧性

```
mono : ⦃ _ : wf f ⦄ → m ℕ.< n → f m < f n
mono (ℕ.s≤s m≤n) with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n  = <-trans (mono m<n) it
... | inj₂ refl = it
```

```agda
inj : ⦃ _ : wf f ⦄ → f m ≡ f n → m ≡ n
inj {m} {n} eq with ℕ.<-cmp m n
... | tri< m<n _ _  = ⊥-elim (<-irrefl eq (mono m<n))
... | tri≈ _ refl _ = refl
... | tri> _ _ n<m  = ⊥-elim (<-irrefl (sym eq) (mono n<m))
```

```agda
<-cmp⊎ : a < c → b < c → a < b ⊎ a ≡ b ⊎ b < a
<-cmp⊎ suc        suc         = inj₂ $ inj₁ refl
<-cmp⊎ suc        (suc₂ b<a)  = inj₂ $ inj₂ b<a
<-cmp⊎ (suc₂ a<b) suc         = inj₁ a<b
<-cmp⊎ (suc₂ a<c) (suc₂ b<c)  = <-cmp⊎ a<c b<c
<-cmp⊎ (lim {n = m}) (lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inj₁ $ mono m<n
... | tri≈ _ refl _ = inj₂ $ inj₁ refl
... | tri> _ _ n<m  = inj₂ $ inj₂ $ mono n<m
<-cmp⊎ (lim {n = m}) (lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (mono m<n) b<f
... | tri≈ _ refl _ = inj₂ $ inj₂ b<f
... | tri> _ _ n<m  = inj₂ $ inj₂ $ <-trans b<f $ mono n<m
<-cmp⊎ (lim₂ {n = m} a<f) (lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inj₁ $ <-trans a<f $ mono m<n
... | tri≈ _ refl _ = inj₁ a<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (mono n<m)
<-cmp⊎ (lim₂ {n = m} a<f) (lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (<-trans a<f (mono m<n)) b<f
... | tri≈ _ refl _ = <-cmp⊎ a<f b<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (<-trans b<f (mono n<m))
```

```agda
<-cmp : a < c → b < c → Tri (a < b) (a ≡ b) (b < a)
<-cmp p q with <-cmp⊎ p q
... | inj₁ a<b = tri< a<b (λ { refl → <-irrefl refl a<b }) (<-asym a<b)
... | inj₂ (inj₁ refl) = tri≈ (<-irrefl refl) refl (<-irrefl refl)
... | inj₂ (inj₂ b<a) = tri> (<-asym b<a) (λ { refl → <-irrefl refl b<a }) b<a
```

**定义** 同株

```agda
_≘_ : Ord → Ord → Set
a ≘ b = ∃[ c ] a ≤ c × b ≤ c
```

```agda
<-trich : a ≘ b → Tri (a < b) (a ≡ b) (b < a)
<-trich (c , inj₁ p , inj₁ q)       = <-cmp p q
<-trich (c , inj₁ p , inj₂ refl)    = tri< p (λ { refl → <-irrefl refl p }) (<-asym p)
<-trich (c , inj₂ refl , inj₁ p)    = tri> (<-asym p) (λ { refl → <-irrefl refl p }) p
<-trich (c , inj₂ refl , inj₂ refl) = tri≈ (<-irrefl refl) refl (<-irrefl refl)

≤-total : a ≘ b → a ≤ b ⊎ b ≤ a
≤-total p with <-trich p
... | tri< p _ _ = inj₁ (inj₁ p)
... | tri≈ _ p _ = inj₁ (inj₂ p)
... | tri> _ _ p = inj₂ (inj₁ p)
```

```agda
≘-refl : a ≘ a
≘-refl = _ , ≤-refl , ≤-refl

≘-sym : a ≘ b → b ≘ a
≘-sym (c , a≤c , b≤c) = c , b≤c , a≤c
```

注意同株不是传递关系.

## 跨树关系

### 前驱

**定义** 前驱深度

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc a) = ⊤ ⊎ Depth a
Depth (lim f) = Σ ℕ λ n → Depth (f n)

private variable δ : Depth a
```

**定义** 前驱运算

```agda
_∸_ : ∀ a → Depth a → Ord; infixl 6 _∸_
suc a ∸ inj₁ tt = a
suc a ∸ inj₂ δ  = a ∸ δ
lim f ∸ (n , δ) = f n ∸ δ
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
  ≼l : a ≼ f n → a ≼ lim f
  ≼l z≼ = z≼
  ≼l (s≼ p) = {!   !} --s≼ p
  ≼l (l≼ p) = l≼ (≼l p)

  ≺l : a ≺ f n → a ≺ lim f
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
s≼s-inj (s≼ {δ = inj₂ δ } p) = {!   !} --≺⇒≼ (s≼ p)
```

```agda
s≺s : a ≺ b → suc a ≺ suc b
s≺s = s≼s

s≺s-inj : suc a ≺ suc b → a ≺ b
s≺s-inj = s≼s-inj
```

```agda
l≼l : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ {n} → f n ≼ g n) → lim f ≼ lim g
l≼l f≼g = l≼ (≼l f≼g)
```

```agda
≼-refl : a ≼ a
≼-refl {a = zero}   = z≼
≼-refl {a = suc _}  = s≼s ≼-refl
≼-refl {a = lim _}  = l≼l ≼-refl
```

### 外延相等

### 严格偏序

## 序数函数

```agda
Func : Set
Func = Ord → Ord
variable F : Func
```

```agda
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
normal {F} mono = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘̇ f) ⦃ mono it ⦄
```

```agda
<mono→≤mono : <-monotonic F → ≤-monotonic F
<mono→≤mono <mono (inj₁ p)    = <⇒≤ (<mono p)
<mono→≤mono <mono (inj₂ refl) = inj₂ refl
```

后继运算严格单调.

```agda
s<s : <-monotonic suc
suc-trans : a < b → b < c → suc a < c

s<s suc         = suc
s<s (suc₂ x<y)  = suc₂ (s<s x<y)
s<s lim         = suc₂ (lim₂ (suc-trans it it))
s<s (lim₂ x<f)  = suc₂ (lim₂ (suc-trans x<f it))

suc-trans a<b suc         = s<s a<b
suc-trans a<b (suc₂ c<b)  = suc₂ (suc-trans a<b c<b)
suc-trans a<f lim         = lim₂ (suc-trans a<f it)
suc-trans a<b (lim₂ b<f)  = lim₂ (suc-trans a<b b<f)
```

推论

```agda
s≤s : ≤-monotonic suc
s≤s (inj₁ a<b)  = inj₁ (s<s a<b)
s≤s (inj₂ refl) = inj₂ refl
```

```agda
s<s-inj : suc a < suc b → a < b
s<s-inj suc         = suc
s<s-inj (suc₂ s<b)  = <-trans suc s<b

s≤s-inj : suc a ≤ suc b → a ≤ b
s≤s-inj (inj₁ s<s)  = inj₁ (s<s-inj s<s)
s≤s-inj (inj₂ refl) = inj₂ refl
```

```agda
<→s≤ : a < b → suc a ≤ b
<→s≤ suc = inj₂ refl
<→s≤ (suc₂ p) = inj₁ (s<s p)
<→s≤ lim = inj₁ (lim₂ {!   !})
<→s≤ (lim₂ p) = {!   !}
```

### 可迭代函数

```agda
record Iterable : Set where
  constructor mkIterable
  field
    _[_] : Func
    <infl : <-inflationary _[_]
```

```agda
variable ℱ : Iterable
open Iterable public
```

```agda
_^⟨_⟩_ : Iterable → Ord → Func
^⟨◌⟩-<mono : <-monotonic (ℱ ^⟨_⟩ i)

ℱ ^⟨ zero ⟩ i = i
ℱ ^⟨ suc a ⟩ i = (ℱ [_] ∘ ℱ ^⟨ a ⟩_) i
ℱ ^⟨ lim f ⟩ i = lim (λ n → ℱ ^⟨ f n ⟩ i) ⦃ ^⟨◌⟩-<mono it ⦄

^⟨◌⟩-<mono {ℱ} {i} {x} suc =                  begin-strict
  ℱ ^⟨ x ⟩ i                                  <⟨ <infl ℱ ⟩
  ℱ [ ℱ ^⟨ x ⟩ i ]  ∎
^⟨◌⟩-<mono {ℱ} {i} {x} (suc₂ {b} p) =         begin-strict
  ℱ ^⟨ x ⟩ i                                  <⟨ ^⟨◌⟩-<mono p ⟩
  ℱ ^⟨ b ⟩ i                                  <⟨ <infl ℱ ⟩
  ℱ [ ℱ ^⟨ b ⟩ i ]                            ∎
^⟨◌⟩-<mono {ℱ} {i} (lim {f} {n}) =            begin-strict
  ℱ ^⟨ f n ⟩ i                                <⟨ lim ⦃ ^⟨◌⟩-<mono it ⦄ ⟩
  lim (λ m → ℱ ^⟨ f m ⟩ i) ⦃ ^⟨◌⟩-<mono it ⦄  ∎
^⟨◌⟩-<mono {ℱ} {i} {x} (lim₂ {f} {n} p) =     begin-strict
  ℱ ^⟨ x ⟩ i                                  <⟨ ^⟨◌⟩-<mono p ⟩
  ℱ ^⟨ f n ⟩ i                                <⟨ lim₂ ⦃ ^⟨◌⟩-<mono it ⦄ (^⟨◌⟩-<mono it) ⟩
  lim (λ m → ℱ ^⟨ f m ⟩ i) ⦃ ^⟨◌⟩-<mono it ⦄  ∎
```

```agda
^⟨◌⟩-≤infl : ≤-inflationary (ℱ ^⟨_⟩ i)
^⟨◌⟩-≤infl {x = zero} = z≤
^⟨◌⟩-≤infl {ℱ} {i} {suc x} =  begin
  suc x                       ≤⟨ s≤s (^⟨◌⟩-≤infl) ⟩
  suc (ℱ ^⟨ x ⟩ i)            ≤⟨ <→s≤ (^⟨◌⟩-<mono suc) ⟩
  ℱ ^⟨ suc x ⟩ i              ∎
^⟨◌⟩-≤infl {x = lim f} = {!   !}
```
