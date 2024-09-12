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
+-pres (lim r) = lim ⦃ _ ⦄ (+-pres r)
+-pres (Lim r) = Lim (+-pres r)
```

```agda
+-infl≤ : β ≤ β + α
+-infl≤ {β} {(zero)} = inr refl
+-infl≤ {β} {suc α} = begin
  β                       ≤⟨ +-infl≤ ⟩
  β + α                   <⟨ +-pres zero ⟩
  β + suc α               ∎ where open HigherRoadReasoning
+-infl≤ {β} {lim f} = begin
  β                       ≤⟨ +-infl≤ ⟩
  β + f 0                 <⟨ +-pres (lim {!   !}) ⟩
  β + lim f               ∎ where open HigherRoadReasoning
+-infl≤ {β} {Lim aℓ F} = begin
  β                       ≤⟨ +-infl≤ ⟩
  β + F (elm 0)           <⟨ +-pres (Lim {!   !}) ⟩
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
```
