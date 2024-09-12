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
