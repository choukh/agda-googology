---
title: 形式化大数数学 (1.5 - 超限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.5 - 超限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Transfinitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Transfinitary.lagda.md)  
> 高亮渲染: [Transfinitary.html](https://choukh.github.io/agda-googology/Veblen.Transfinitary.html)  

```agda
{-# OPTIONS --lossy-unification --rewriting --local-confluence-check #-}
module Veblen.Transfinitary where
open import Veblen.Basic public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
```

## 超限元函数类型

```agda
_→^_ : Set → Ord → Set
A →^ zero = A
A →^ suc α = Ord → A →^ α
A →^ lim f = ∀ {n} → Ord → A →^ f n
```

```agda
_0̇ : A →^ α → A
_0̇ {α = zero} = id
_0̇ {α = suc _} F = F 0 0̇
_0̇ {α = lim _} F = F {0} 0 0̇
```

```agda
_0̇,_ : A →^ suc α → A →^ 1
_0̇,_ {α = zero} = id
_0̇,_ {α = suc _} F = F 0 0̇,_
_0̇,_ {α = lim _} F = F 0 {0} 0̇,_
```

## 超限元Veblen函数

```agda
Φₛ : Ord →^ suc α → Ord →^ 2+ α
Φₗ : Ord →^ lim f → Ord →^ suc (lim f)
Φ : Ord →^ 1 → (∀ {α} → Ord →^ suc α)
```

```agda
Φₛ F = rec F
  (λ φ-α → Φ $ fixpt λ β → φ-α β 0̇)
  (λ φ[_] → Φ $ jump λ β → lim λ n → φ[ n ] β 0̇)
```

```agda
Φₗ F = rec F
  (λ φ-α  → Φ $ jump⟨ 1 ⟩ λ β → lim λ n → φ-α {n} β 0̇)
  (λ φ[_] → Φ $ jump (λ β → lim λ m → φ[ m ] {m} β 0̇))
```

```agda
Φ F {α = zero}  = F
Φ F {α = suc α} = Φₛ (Φ F)
Φ F {α = lim f} = Φₗ (Φ F)
```

```agda
φ : ∀ {α} → Ord →^ suc α
φ = Φ (ω ^_)
```

```agda
SVO : Ord
SVO = φ {ω} 1 {0} 0
```

```agda
LVO : Ord
LVO = fixpt (λ α → φ {α} 1 0̇) 0
```

```agda
Φ-ż-α : Φ F {α} 0̇,_ ≡ F
Φ-ż-α {α = zero} = refl
Φ-ż-α {α = suc α} = Φ-ż-α {α = α}
Φ-ż-α {α = lim f} = Φ-ż-α {α = f 0}
{-# REWRITE Φ-ż-α #-}
```

```agda
Φ-s-ż-z : (Φ F {suc α} (suc β) 0̇, 0) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) 0
Φ-s-ż-z = refl
```
