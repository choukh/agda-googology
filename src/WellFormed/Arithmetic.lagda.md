---
title: 形式化大数数学 (2.2 - 序数算术)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.2 - 序数算术)

> 交流Q群: 893531731  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-googology/WellFormed.Arithmetic.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Arithmetic where
open import WellFormed.Base
open import WellFormed.Properties
```

```agda
private
  pres = ^⟨*⟩-pres<
  instance
    _ = z≤
    _ = ≤-refl
    _ : NonZero (suc a)
    _ = _
    _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
    _ = _
```

## 加法

```agda
Suc : EverInfl 0
Suc = everInfl (λ x → suc x) zero₁
```

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
a + b = Suc ^⟨ b ⟩ a
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = normal (a +_) pres refl
```

```agda
+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
+-assoc a b zero = refl
+-assoc a b (suc c) = cong suc (+-assoc a b c)
+-assoc a b (lim f) = limExt ⦃ pres (pres it) ⦄ ⦃ pres it ⦄ λ n → +-assoc a b (f n)
```

```agda
+-idʳ : a + 0 ≡ a
+-idʳ = refl
```

```agda
+-idˡ : ∀ a → 0 + a ≡ a
+-idˡ zero = refl
+-idˡ (suc a) = cong suc (+-idˡ a)
+-idˡ (lim f) = limExt ⦃ pres it ⦄ λ n → +-idˡ (f n)
```

## 乘法

```agda
RightAdd : (b : Ord) → ⦃ NonZero b ⦄ → EverInfl 0
RightAdd b = Suc ^⟨ b ⟩
```

```agda
_⋅_ : (a : Ord) → ⦃ NonZero a ⦄ → Ord → Ord; infixl 7 _⋅_
a ⋅ b = (RightAdd a) ^⟨ b ⟩ 0
```

```agda
LeftMul : (a : Ord) → ⦃ NonZero a ⦄ → Normal
LeftMul a = normal (a ⋅_) pres refl
```

```agda
⋅-idʳ : ∀ a → ⦃ _ : NonZero a ⦄ → a ⋅ 1 ≡ a
⋅-idʳ a =     begin-equality
  a ⋅ 1       ≈⟨ refl ⟩
  a ⋅ 0 + a   ≈⟨ cong (_+ a) refl ⟩
  0 + a       ≈⟨ +-idˡ a ⟩
  a           ∎ where open SubTreeReasoning
```

## 幂

```agda
RightMul : (b : Ord) → ⦃ NonTrivial b ⦄ → EverInfl 1
RightMul b = everInfl _⋅b infl where
  instance _ : ⦃ 1 ≤ a ⦄ → NonZero a
  _ = nz-intro (s≤→< it)
  _⋅b : Func↾ 1
  (x ⋅b) = (x ⋅ b)
  infl : _⋅b inflates _<_ from 1
  infl {x} =  begin-strict
    x         ≈˘⟨ ⋅-idʳ x ⟩
    (x ⋅ 1)   <⟨ pres nt-elim ⟩
    x ⋅b      ∎ where open SubTreeReasoning
```

```agda
_^_ : (a : Ord) → ⦃ NonTrivial a ⦄ → Ord → Ord; infix 8 _^_
a ^ b = (RightMul a) ^⟨ b ⟩ 1
```

```agda
LeftExp : (a : Ord) → ⦃ NonTrivial a ⦄ → Normal
LeftExp a = normal (a ^_) pres refl
```
