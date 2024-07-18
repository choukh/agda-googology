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
private instance
  _ = z≤
  _ = ≤-refl
```

```agda
Suc : Iterable
Suc = iterable 0 (λ x → suc x) suc
```

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
a + b = Suc ^⟨ b ⟩ a
```

```agda
RightAdd : (b : Ord) → ⦃ NonZero b ⦄ → Iterable
RightAdd b = Suc ^⟨ b ⟩
```

```agda
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _*_
a * b = RightAdd a ^⟨ b ⟩ 0
```

```agda
RightMult : (b : Ord) → ⦃ NonTrivial b ⦄ → Iterable
RightMult b = iterable 1 *b infl
  where
  *b : Func↾ 1
  *b x ⦃ i≤ ⦄ = (x * b) ⦃ nonZero-intro (s≤→< i≤) ⦄
  infl : *b inflates _<_ from 1
  infl = {!   !}
```

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 8 _^_
a ^ b = RightMult a ^⟨ b ⟩ 1
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = normal (a +_) ^⟨◌⟩-pres< refl

LeftMult : (a : Ord) → ⦃ NonZero a ⦄ → Normal
LeftMult a = normal (a *_) ^⟨◌⟩-pres< refl

LeftPow : (a : Ord) → ⦃ NonTrivial a ⦄ → Normal
LeftPow a = normal (a ^_) ^⟨◌⟩-pres< refl
```
