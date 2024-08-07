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

## 加法

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
+-pres-rd : (a +_) preserves Road

+-pres< : (a +_) preserves _<_
+-pres< = map +-pres-rd
```

```agda
a + zero = a
a + suc b = suc (a + b)
a + lim f = lim (λ n → a + f n) ⦃ +-pres< it ⦄

+-pres-rd zero = zero
+-pres-rd (suc r) = suc (+-pres-rd r)
+-pres-rd (lim r) = lim ⦃ +-pres< it ⦄ (+-pres-rd r)
```

```agda
+-idʳ : a + 0 ≡ a
+-idʳ = refl
```

```agda
+-idˡ : 0 + a ≡ a
+-idˡ {(zero)} = refl
+-idˡ {suc a} = cong suc +-idˡ
+-idˡ {lim f} = limExt ⦃ +-pres< it ⦄ λ _ → +-idˡ
```

```agda
+-assoc : a + (b + c) ≡ (a + b) + c
+-assoc {c = zero} = refl
+-assoc {c = suc _} = cong suc +-assoc
+-assoc {c = lim _} = limExt ⦃ +-pres< (+-pres< it) ⦄ ⦃ +-pres< it ⦄ λ _ → +-assoc
```

```agda
+-infl≤ : (_+ b) inflates _≤_
+-infl≤ {b = zero} = inr refl
+-infl≤ {b = suc b} {x} = begin
  x                       ≤⟨ +-infl≤ ⟩
  x + b                   <⟨ +-pres< zero₁ ⟩
  x + suc b               ∎ where open SubTreeReasoning
+-infl≤ {b = lim f} {x} = begin
  x                       ≤⟨ +-infl≤ ⟩
  x + f 0                 <⟨ f<l ⦃ +-pres< it ⦄ ⟩
  x + lim f               ∎ where open SubTreeReasoning
```

```agda
+-infl< : ⦃ NonZero b ⦄ → (_+ b) inflates _<_
+-infl< {b = suc b} {x} = begin-strict
  x                       ≤⟨ +-infl≤ ⟩
  x + b                   <⟨ +-pres< zero₁ ⟩
  x + suc b               ∎ where open SubTreeReasoning
+-infl< {b = lim f} {x} = begin-strict
  x                       ≤⟨ +-infl≤ ⟩
  x + f 0                 <⟨ f<l ⦃ +-pres< it ⦄ ⟩
  x + lim f               ∎ where open SubTreeReasoning
```

## 乘法

```agda
_*_ : (a : Ord) → ⦃ NonZero a ⦄ → Ord → Ord; infixl 7 _*_
*-pres-rd : ⦃ _ : NonZero a ⦄ → (a *_) preserves Road

*-pres< : ⦃ _ : NonZero a ⦄ → (a *_) preserves _<_
*-pres< = map *-pres-rd
```

```agda
a * zero = 0
a * suc b = a * b + a
a * lim f = lim (λ n → a * f n) ⦃ *-pres< it ⦄

*-pres-rd zero = set +-infl<
*-pres-rd {a} {x} (suc {b} r) = begin-strict
  a * x                   <⟨ *-pres-rd r ⟩
  a * b                   <⟨ set +-infl< ⟩
  a * b + a               ∎ where open RoadReasoning
*-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a * x                   <⟨ *-pres-rd r ⟩
  a * f n                 <⟨ set (f<l ⦃ *-pres< it ⦄) ⟩
  a * lim f               ∎ where open RoadReasoning
```

```agda
*-zʳ : ⦃ _ : NonZero a ⦄ → a * 0 ≡ 0
*-zʳ = refl
```

```agda
*-idʳ : ⦃ _ : NonZero a ⦄ → a * 1 ≡ a
*-idʳ {a} =               begin-equality
  a * 1                   ≈⟨ refl ⟩
  a * 0 + a               ≈⟨ cong (_+ a) refl ⟩
  0 + a                   ≈⟨ +-idˡ ⟩
  a                       ∎ where open SubTreeReasoning
```

```agda
*-idˡ : 1 * a ≡ a
*-idˡ {(zero)} = refl
*-idˡ {suc a} = cong suc *-idˡ
*-idˡ {lim f} = limExt ⦃ *-pres< it ⦄ λ _ → *-idˡ
```

```
*-2 : ⦃ _ : NonZero a ⦄ → a * 2 ≡ a + a
*-2 {a} =                 begin-equality
  a * 2                   ≈⟨ refl ⟩
  a * 1 + a               ≈⟨ cong (_+ a) *-idʳ ⟩
  a + a                   ∎ where open SubTreeReasoning
```

```agda
*-distrib : ⦃ _ : NonZero a ⦄ → a * (b + c) ≡ a * b + a * c
*-distrib {c = zero} = refl
*-distrib {a} {b} {c = suc c} = begin-equality
  a * (b + suc c)         ≈⟨ refl ⟩
  a * (b + c) + a         ≈⟨ cong (_+ a) *-distrib ⟩
  a * b + a * c + a       ≈˘⟨ +-assoc ⟩
  a * b + (a * c + a)     ≈⟨ refl ⟩
  a * b + (a * suc c)     ∎ where open SubTreeReasoning
*-distrib {c = lim f} = limExt ⦃ *-pres< (+-pres< it) ⦄ ⦃ +-pres< (*-pres< it) ⦄ λ _ → *-distrib
```

```agda
*-nz : ⦃ _ : NonZero a ⦄ ⦃ _ : NonZero b ⦄ → NonZero (a * b)
*-nz {a = suc a} {b = suc b} = _
*-nz {a = suc a} {b = lim f} = _
*-nz {a = lim f} {b = suc b} = _
*-nz {a = lim f} {b = lim f₁} = _
```

```agda
module _ {a} {b} ⦃ _ : NonZero a ⦄ ⦃ _ : NonZero b ⦄ where
  instance _ = *-nz {a} {b}
  *-assoc : a * (b * c) ≡ (a * b) * c
  *-assoc {c = zero}  = refl
  *-assoc {c = suc c} =   begin-equality
    a * (b * suc c)       ≈⟨ refl ⟩
    a * (b * c + b)       ≈⟨ *-distrib ⟩
    a * (b * c) + a * b   ≈⟨ cong (_+ a * b) *-assoc ⟩
    a * b * c + a * b     ≈⟨ refl ⟩
    a * b * suc c         ∎ where open SubTreeReasoning
  *-assoc {c = lim f} = limExt ⦃ *-pres< (*-pres< it) ⦄ ⦃ *-pres< it ⦄ λ _ → *-assoc
```

## 幂运算

```agda
_^_ : (a : Ord) → ⦃ NonTrivial a ⦄ → Ord → Ord; infix 8 _^_
^-nz : ⦃ _ : NonTrivial a ⦄ → NonZero (a ^ b)

a ^ zero = 1
a ^ suc b = a ^ b * a where instance _ = ^-nz
a ^ lim f = lim (λ n → a ^ f n) ⦃ {!   !} ⦄

^-nz {b = zero} = _
^-nz {b = suc b} = *-nz ⦃ ^-nz ⦄ ⦃ nt-nz ⦄
^-nz {b = lim f} = _
```
