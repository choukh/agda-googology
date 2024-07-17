---
title: 形式化大数数学 (2.1 - 序数算术)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.1 - 序数算术)

> 交流Q群: 893531731  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-googology/WellFormed.Arithmetic.html)  

```agda
{-# OPTIONS --safe #-}
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
RightAdd a = iterable (_+ a) (^⟨⟩◌-infl< (inj₁ suc))
```

```agda
_*_ : (a : Ord) → ⦃ NonZero a ⦄ → Ord → Ord; infixl 7 _*_
a * b = RightAdd a ^⟨ b ⟩ 0
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = normal (a +_) ^⟨◌⟩-pres< refl
```
