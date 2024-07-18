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
private
  instance
    _ = z≤
    _ = ≤-refl
  pres = ^⟨◌⟩-pres<
```

```agda
open import Algebra.Definitions {A = Ord} _≃_
```

## 加法

```agda
Suc : Iterable
Suc = iterable 0 (λ x → suc x) suc
```

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
a + b = Suc ^⟨ b ⟩ a
```

```agda
+-assoc : Associative _+_
+-assoc _ _ zero = ≃-refl
+-assoc a b (suc c) = s≃s (+-assoc a b c)
+-assoc a b (lim f) = l≃l ⦃ pres it ⦄ ⦃ pres $ pres it ⦄ (+-assoc a b (f _))
```

## 乘法

```agda
RightAdd : (b : Ord) → ⦃ NonZero b ⦄ → Iterable
RightAdd b = Suc ^⟨ b ⟩
```

```agda
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _*_
a * b = RightAdd a ^⟨ b ⟩ 0
```

```agda
RightMult : (b : Ord) → ⦃ ntb : NonTrivial b ⦄ → Iterable
RightMult b ⦃ ntb ⦄ = iterable 1 _*b infl
  where
  _*b : Func↾ 1
  (x *b) ⦃ i≤ ⦄ = (x * b) ⦃ nonZero-intro (s≤→< i≤) ⦄
  infl : _*b inflates _<_ from 1
  infl {x} ⦃ i≤ ⦄ =                     begin-strict
    x                                   ≈⟨ {! pres  !} ⟩
    (x * 1) ⦃ nonZero-intro (s≤→< i≤) ⦄ <⟨ pres {!   !} ⟩
    x *b                                ∎ where open SubTreeReasoning
```

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 8 _^_
a ^ b = RightMult a ^⟨ b ⟩ 1
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = normal (a +_) pres refl

LeftMult : (a : Ord) → ⦃ NonZero a ⦄ → Normal
LeftMult a = normal (a *_) pres refl

LeftPow : (a : Ord) → ⦃ NonTrivial a ⦄ → Normal
LeftPow a = normal (a ^_) pres refl
```
