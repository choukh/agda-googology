---
title: 形式化大数数学 (2.1 - 序数算术)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.1 - 序数算术)

> 交流Q群: 893531731  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-googology/WellFormed.Arithmetic.html)  

```agda
{-# OPTIONS --safe --lossy-unification #-}
module WellFormed.Arithmetic where
open import WellFormed.Base
```

```agda
Suc : Iterable
Suc = iterable suc suc
```

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
a + b = Suc ^⟨ b ⟩ a
```

```agda
RightAdd : (a : Ord) → ⦃ NonZero a ⦄ → Iterable
RightAdd a = iterable (_+ a) ^⟨⟩◌-infl<
```

```agda
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _*_
a * b = RightAdd a ^⟨ b ⟩ 0
```

```agda
RightMult : (a : Ord) → ⦃ NonZero a ⦄ → Iterable
RightMult a = iterable {!  1 * a !} {!   !}
```

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 8 _^_
^-nonZero : ⦃ _ : NonTrivial a ⦄ → NonZero (a ^ b)

a ^ zero = 1
a ^ suc b = (a ^ b * a) ⦃ ^-nonZero ⦄
a ^ lim f = lim (λ n → a ^ f n) ⦃ {!   !} ⦄

^-nonZero {a} {b = zero} = _
^-nonZero {a} {b = suc b} = {!   !}
^-nonZero {a} {b = lim f} = _
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = normal (a +_) ^⟨◌⟩-pres< refl

LeftMult : (a : Ord) → ⦃ NonZero a ⦄ → Normal
LeftMult a = normal (a *_) ^⟨◌⟩-pres< refl
```
