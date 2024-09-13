---
title: 形式化大数数学 (3.1 - 序数崩塌函数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.1 - 序数崩塌函数)

> 交流Q群: 893531731  
> 本文源码: [Collapsing.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/Madore/Collapsing.lagda.md)  
> 高亮渲染: [Collapsing.html](httrsps://choukh.github.io/agda-googology/Madore.Collapsing.html)  

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module Madore.Collapsing where
open import Madore.HigherOrd public
```

## 一些约定

```agda
nonZero : Ord a → Type
nonZero zero = ⊥
nonZero _ = ⊤

record NonZero (α : Ord a) : Type where
  field .wrap : nonZero α
```

```agda
nonTrivial : Ord a → Type
nonTrivial zero       = ⊥
nonTrivial (suc zero) = ⊥
nonTrivial _          = ⊤

record NonTrivial (α : Ord a) : Type where
  field .wrap : nonTrivial α
```

## 高阶算术

```agda
_+_ : Ord a → Ord a → Ord a; infixl 7 _+_
+-pres : β < γ → α + β < α + γ

α + zero = α
α + suc β = suc (α + β)
α + lim f = lim (λ n → α + f n) ⦃ map +-pres it ⦄
α + Lim aℓ F = Lim aℓ (λ ι → α + F ι)

+-pres zero = zero
+-pres (suc r) = suc (+-pres r)
+-pres (lim r) = lim (+-pres r)
+-pres (Lim r) = Lim (+-pres r)
+-pres f<l = f<l
```

```agda
+-infl≤ : Wf α → β ≤ β + α
+-infl≤ zero = inr refl
+-infl≤ {α = suc α} {β} (suc α̇) = begin
  β                       ≤⟨ +-infl≤ α̇ ⟩
  β + α                   <⟨ +-pres zero ⟩
  β + suc α               ∎ where open HigherRoadReasoning
+-infl≤ {α = lim f} {β} (lim ḟ) = begin
  β                       ≤⟨ +-infl≤ ḟ ⟩
  β + f 0                 <⟨ +-pres f<l ⟩
  β + lim f               ∎ where open HigherRoadReasoning
+-infl≤ {α = Lim aℓ F} {β} (Lim Ḟ F-pres) = begin
  β                       ≤⟨ +-infl≤ (Ḟ {0}) ⟩
  β + F (elm 0)           <⟨ +-pres $ Lim $ F-pres zero ⟩
  β + Lim aℓ F            ∎ where open HigherRoadReasoning
```

```agda
_*_ : (α : Ord a) → Ord a → ⦃ NonZero α ⦄ → Ord a; infixl 8 _*_
*-pres : ⦃ _ : NonZero α ⦄ → β < γ → α * β < α * γ

α * zero = 0
α * suc β = α * β + α
α * lim f = lim (λ n → α * f n) ⦃ map *-pres it ⦄
α * Lim aℓ F = Lim aℓ (λ ι → α * F ι)

*-pres zero = {!   !}
*-pres (suc r) = {!   !}
*-pres (lim r) = {!   !}
*-pres (Lim r) = {!   !}
*-pres f<l = {!   !}
```
