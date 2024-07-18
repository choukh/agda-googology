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
open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
--postulate
--  ext : Extensionality 0ℓ 0ℓ
```

```agda
ex : (f g : Seq) ⦃ f⇡ : f ⇡ ⦄ ⦃ g⇡ : g ⇡ ⦄ → f ≡ g → lim f ≡ lim g
ex f g refl = {! refl  !}
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

```agda
+-assoc : ∀ a b c → a + b + c ≡ a + (b + c)
+-assoc _ _ zero = refl --≃-refl
+-assoc a b (suc c) = cong suc (+-assoc a b c) --s≃s (+-assoc a b c)
+-assoc a b (lim f) = {!  cong lim !} --l≃l ⦃ pres it ⦄ ⦃ pres $ pres it ⦄ (+-assoc a b (f _))
```

```agda
+-idˡ : ∀ a → 0 + a ≡ a
+-idˡ zero    = refl
+-idˡ (suc a) = cong suc (+-idˡ a)
+-idˡ (lim f) = {!  cong lim !} --l≃l ⦃ pres it ⦄ ⦃ it ⦄ (+-idˡ (f _))
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

```agda
*-idʳ : (a : Ord) → ⦃ _ : NonZero a ⦄ → a * 1 ≡ a
*-idʳ (suc a) = cong suc {!   !}
*-idʳ (lim f) = {!   !}
```

## 幂

```agda
◌*_ : (b : Ord) → ⦃ ntb : NonTrivial b ⦄ → Iterable
◌*_ b ⦃ ntb ⦄ = iterable 1 _*b infl
  where
  _*b : Func↾ 1
  (x *b) ⦃ i≤ ⦄ = (x * b) ⦃ nonZero-intro (s≤→< i≤) ⦄
  infl : _*b inflates _<_ from 1
  infl {x} ⦃ i≤ ⦄ =                     begin-strict
    x                                   ≈˘⟨ *-idʳ x ⦃ {!   !} ⦄ ⟩
    (x * 1) ⦃ nonZero-intro (s≤→< i≤) ⦄ <⟨ pres {!   !} ⟩
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
