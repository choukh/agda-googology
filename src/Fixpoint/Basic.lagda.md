---
title: 形式化大数数学(1) - 基础
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学(1) - 基础

> 交流Q群: 893531731  
> 本文源码: [Basic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Fixpoint/Basic.lagda.md)  
> 高亮渲染: [Basic.html](https://choukh.github.io/agda-googology/Fixpoint.Basic.html)  

## 前言

```agda
module Fixpoint.Basic where

open import Data.Nat public using (ℕ; zero; suc; 2+)
open import Data.Unit public using (⊤)
open import Function public using (id; _∘_; _$_; _∋_)
open import Relation.Binary.PropositionalEquality as Eq public using (_≡_; refl; cong)
open Eq.≡-Reasoning
```

## 序数的定义

```agda
data Ord : Set where
  zero : Ord
  suc  : Ord → Ord
  lim  : (ℕ → Ord) → Ord
```

```agda
variable
  α β γ δ : Ord
  m n : ℕ
```

```agda
finord : ℕ → Ord
finord zero = zero
finord (suc n) = suc (finord n)
```

```agda
ω = lim finord
```

```agda
open import Agda.Builtin.FromNat

instance
  _ = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord n }
  _ = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
```

```agda
_ = Ord ∋ 233
_ = ℕ   ∋ 233
```

## 快速增长层级

```agda
variable A : Set
```

```agda
_∘ⁿ_ : (A → A) → ℕ → (A → A)
(F ∘ⁿ zero)  a = a
(F ∘ⁿ suc n) a = (F ∘ (F ∘ⁿ n)) a
```

```agda
module FGH where
  f : Ord → ℕ → ℕ
  f zero n = suc n
  f (suc α) n = (f α ∘ⁿ n) n
  f (lim g) n = f (g n) n
```

$$
f_0(n) = n + 1
$$

```agda
  f-0-2 : f 0 2 ≡ 3
  f-0-2 = refl
```

$$
f_1(n) = 2n
$$

```agda
  f-1-2 : f 1 2 ≡ 4
  f-1-2 = refl
```

$$
f_2(n) = 2^n~n
$$

```agda
  f-2-2 : f 2 2 ≡ 8
  f-2-2 = refl
```

```agda
  f-3-2 : f 3 2 ≡ 2048
  f-3-2 = refl
```

```agda
  f-suc : f (suc α) n ≡ (f α ∘ⁿ n) n
  f-suc = refl
```

```agda
  f-ω : f ω n ≡ f (finord n) n
  f-ω = refl
```

```agda
  f-ω⁺ : f (suc ω) n ≡ (f ω ∘ⁿ n) n
  f-ω⁺ = refl
```

```agda
  f-suc-2 : f (suc α) 2 ≡ f α (f α 2)
  f-suc-2 = refl
```

`f (suc ω) 64` 大于葛立恒数.

## 无穷迭代

```agda
elim : {P : Ord → Set}
  → P zero
  → (∀ α → P α → P (suc α))
  → (∀ f → (∀ n → P (f n)) → P (lim f))
  → ∀ α → P α
elim z s l zero = z
elim z s l (suc α) = s α (elim z s l α)
elim z s l (lim f) = l f λ n → elim z s l (f n)
```

```agda
rec : A → (A → A) → ((ℕ → A) → A) → Ord → A
rec z s l = elim z (λ _ → s) (λ _ → l)
```

```agda
_∘^_ : (Ord → Ord) → Ord → Ord → Ord
(F ∘^ α) β = rec β F lim α
```

```agda
variable
  F : Ord → Ord
  f g h : ℕ → Ord
```

```agda
∘^-zero : F ∘^ zero ≡ id
∘^-zero = refl
```

```agda
∘^-suc : F ∘^ suc α ≡ F ∘ (F ∘^ α)
∘^-suc = refl
```

```agda
∘^-lim : F ∘^ lim f ≡ λ β → lim λ n → (F ∘^ (f n)) β
∘^-lim = refl
```

```agda
iterω : (Ord → Ord) → Ord → Ord
iterω F α = (F ∘^ ω) α
```

## 序数算术

```agda
infixl 6 _+_
_+_ : Ord → Ord → Ord
α + β = (suc ∘^ β) α
```

```agda
infixl 7 _*_
_*_ : Ord → Ord → Ord
α * β = ((_+ α) ∘^ β) 0
```

```agda
infix 8 _^_
_^_ : Ord → Ord → Ord
α ^ β = ((_* α) ∘^ β) 1
```

```agda
_+ω^_ : Ord → Ord → Ord
α +ω^ zero = suc α
α +ω^ suc β = iterω (_+ω^ β) α
α +ω^ lim f = lim λ n → α +ω^ f n
```

## 跳出运算

复合了后继的迭代.

```agda
jump : (Ord → Ord) → Ord → Ord
jump F α = ((F ∘ suc) ∘^ α) (F zero)
```

```agda
jump-0 : jump F 0 ≡ F 0
jump-0 = refl
```

```agda
jump-suc : jump F (suc α) ≡ F (suc (jump F α))
jump-suc {F} {α} = begin
  jump F (suc α)                        ≡⟨⟩
  ((F ∘ suc) ∘^ (suc α)) (F zero)       ≡⟨⟩
  (F ∘ suc) (((F ∘ suc) ∘^ α) (F zero)) ≡⟨⟩
  F (suc (jump F α))                    ∎
```

```agda
jump-lim : jump F (lim f) ≡ lim λ n → jump F (f n)
jump-lim = refl
```

## 不动点的枚举

```agda
fixpt : (Ord → Ord) → Ord → Ord
fixpt F = jump (iterω F)
```

```agda
fixpt-0 : fixpt F 0 ≡ iterω F 0
fixpt-0 = refl
```

```agda
fixpt-suc : fixpt F (suc α) ≡ iterω F (suc (fixpt F α))
fixpt-suc {F} {α} = refl
```

```agda
fixpt-lim : fixpt F (lim f) ≡ lim λ n → fixpt F (f n)
fixpt-lim = refl
```

## ε， ζ， η 层级

```agda
ε : Ord → Ord
ε = fixpt (ω ^_)
```

```agda
ε-0 : ε 0 ≡ iterω (ω ^_) 0
ε-0 = refl
```

```agda
ε-suc : ε (suc α) ≡ iterω (ω ^_) (suc (ε α))
ε-suc = refl
```

```agda
ε-lim : ε (lim f) ≡ lim λ n → ε (f n)
ε-lim = refl
```

```agda
ζ : Ord → Ord
ζ = fixpt ε
```

```agda
η : Ord → Ord
η = fixpt ζ
```
