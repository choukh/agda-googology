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
  pres = ^⟨◌⟩-pres<
  instance
    _ = z≤
    _ = ≤-refl
    _ : NonZero (suc a)
    _ = _
    _ : ⦃ _ : f ⇡ ⦄ → NonZero (lim f)
    _ = _
```

**约定** 非平凡序数指不等于零或一的序数.

```agda
not01 : Ord → Set
not01 zero       = ⊥
not01 (suc zero) = ⊥
not01 _          = ⊤

record NonTrivial (a : Ord) : Set where
  field nonTrivial : not01 a
```

```agda
nt-intro : 1 < a → NonTrivial a
nt-intro {suc zero} (suc₂ ())
nt-intro {2+ a}         _ = _
nt-intro {suc (lim _)}  _ = _
nt-intro {lim _}        _ = _

nt-elim : ⦃ NonTrivial a ⦄ → 1 < a
nt-elim {2+ _}        = s<s z<s
nt-elim {suc (lim _)} = s<s z<l
nt-elim {lim f}       = lim₂ (n<fs f 1)
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
_+◌ : (a : Ord) → Normal
a +◌ = normal (a +_) pres refl
```

## 乘法

```agda
◌+_ : (b : Ord) → ⦃ NonZero b ⦄ → Iterable
◌+ b = Suc ^⟨ b ⟩
```

```agda
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _*_
a * b = (◌+ a) ^⟨ b ⟩ 0
```

```agda
_*◌ : (a : Ord) → ⦃ NonZero a ⦄ → Normal
a *◌ = normal (a *_) pres refl
```

## 幂

```agda
◌*_ : (b : Ord) → ⦃ NonTrivial b ⦄ → Iterable
◌*_ b = iterable 1 _*b infl
  where
  _*b : Func↾ 1
  (x *b) ⦃ i≤ ⦄ = (x * b) ⦃ nz-intro (s≤→< i≤) ⦄
  infl : _*b inflates _<_ from 1
  infl {x} ⦃ i≤ ⦄ =                     begin-strict
    x                                   ≈⟨ {!   !} ⟩
    (x * 1) ⦃ nz-intro (s≤→< i≤) ⦄      <⟨ pres nt-elim ⟩
    x *b                                ∎ where open SubTreeReasoning
```

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 8 _^_
a ^ b = (◌* a) ^⟨ b ⟩ 1
```

```agda
_^◌ : (a : Ord) → ⦃ NonTrivial a ⦄ → Normal
a ^◌ = normal (a ^_) pres refl
```
 