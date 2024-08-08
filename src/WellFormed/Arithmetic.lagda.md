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
Func↾ : (Ord → Type) → Type
Func↾ P = (x : Ord) ⦃ p : P x ⦄ → Ord

_↾_ : Func → (P : Ord → Type) → Func↾ P
F ↾ P = λ a → F a
```

```agda
restricted-infl-syntax : {P : Ord → Type} → Func↾ P → Rel → Type
restricted-infl-syntax {P} F _~_ = ∀ {x} ⦃ p : P x ⦄ → x ~ F x
syntax restricted-infl-syntax {P} F _~_ = F inflates _~_ within P
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
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _*_
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
  a * f n                 <⟨ set $ f<l ⦃ *-pres< it ⦄ ⟩
  a * lim f               ∎ where open RoadReasoning
```

```agda
*-congˡ : ⦃ nza : NonZero a ⦄ ⦃ nzb : NonZero b ⦄ → a ≡ b → a * c ≡ b * c
*-congˡ refl = refl
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
*-distrib {c = lim _} = limExt ⦃ *-pres< (+-pres< it) ⦄ ⦃ +-pres< (*-pres< it) ⦄ λ _ → *-distrib
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
  *-assoc {c = lim _} = limExt ⦃ *-pres< (*-pres< it) ⦄ ⦃ *-pres< it ⦄ λ _ → *-assoc
```

```agda
*-infl< : ⦃ NonTrivial b ⦄ → (_* b) inflates _<_ within NonZero
*-infl< {b} {x} =         begin-strict
  x                       ≈˘⟨ *-idʳ ⟩
  x * 1                   <⟨ *-pres< nt-elim ⟩
  x * b                   ∎ where open SubTreeReasoning
```

## 幂运算

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 8 _^_
^-nz : ⦃ _ : NonTrivial a ⦄ → NonZero (a ^ b)
^-pres-rd : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves Road

^-pres< : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _<_
^-pres< = map ^-pres-rd
```

```agda
a ^ zero = 1
a ^ suc b = a ^ b * a where instance _ = ^-nz
a ^ lim f = lim (λ n → a ^ f n) ⦃ ^-pres< it ⦄

^-nz {b = zero} = _
^-nz {b = suc b} = *-nz ⦃ ^-nz ⦄ ⦃ nt-nz ⦄
^-nz {b = lim f} = _

^-pres-rd zero = set *-infl< where instance _ = ^-nz
^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ b                   <⟨ set *-infl< ⟩
  a ^ b * a               ∎ where open RoadReasoning; instance _ = ^-nz
^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ f n                 <⟨ set $ f<l ⦃ ^-pres< it ⦄ ⟩
  a ^ lim f               ∎ where open RoadReasoning
```

```agda
^-idʳ : ⦃ _ : NonTrivial a ⦄ → a ^ 1 ≡ a
^-idʳ {a} =               begin-equality
  a ^ 1                   ≈⟨ refl ⟩
  a ^ 0 * a               ≈⟨ refl ⟩
  1 * a                   ≈⟨ *-idˡ ⟩
  a                       ∎ where open SubTreeReasoning
```

```agda
module _ {a} {b} ⦃ _ : NonTrivial a ⦄ where
  instance _ = ^-nz {a}
  ^-distrib : a ^ (b + c) ≡ a ^ b * a ^ c
  ^-distrib {c = zero} = sym +-idˡ
  ^-distrib {c = suc c} =       begin-equality
    a ^ (b + suc c)             ≈⟨ refl ⟩
    a ^ (b + c) * a             ≈⟨ *-congˡ ⦃ nzb = *-nz ⦄ ^-distrib ⟩
    (a ^ b * a ^ c * a) ⦃ _ ⦄   ≈˘⟨ *-assoc ⟩
    a ^ b * (a ^ c * a)         ≈⟨ refl ⟩
    a ^ b * (a ^ suc c)         ∎ where open SubTreeReasoning
  ^-distrib {c = lim _} = limExt ⦃ ^-pres< (+-pres< it) ⦄ ⦃ *-pres< (^-pres< it) ⦄ λ _ → ^-distrib
```

```agda
^-nt : ⦃ nta : NonTrivial a ⦄ ⦃ nzb : NonZero b ⦄ → NonTrivial (a ^ b)
^-nt {suc a} {suc b} ⦃ nzb ⦄ =  nt-intro $ begin-strict
  1                             ≈⟨ refl ⟩
  suc a ^ 0                     ≤⟨ pres<→pres≤ ^-pres< $ <s→≤ (nz-elim ⦃ nzb ⦄) ⟩
  suc a ^ b                     ≈˘⟨ *-idʳ ⟩
  suc a ^ b * 1                 ≤⟨ pres<→pres≤ *-pres< $ <s→≤ nt-elim ⟩
  suc a ^ b * a                 <⟨ +-infl< ⟩
  suc a ^ b * a + suc a ^ b     ∎ where open SubTreeReasoning; instance _ = ^-nz
^-nt {lim f} {suc b} = _
^-nt {suc a} {lim f} = _
^-nt {lim f} {lim g} = _
```

```agda
module _ {a} {b} ⦃ _ : NonTrivial a ⦄ ⦃ _ : NonZero b ⦄ where
  instance _ = ^-nt {a} {b}
  ^-assoc : (a ^ b) ^ c ≡ a ^ (b * c)
  ^-assoc {c = zero} = refl
  ^-assoc {c = suc c} =         begin-equality
    (a ^ b) ^ suc c             ≈⟨ refl ⟩
    ((a ^ b) ^ c * a ^ b) ⦃ _ ⦄ ≈⟨ *-congˡ ⦃ ^-nz ⦄ ⦃ ^-nz ⦄ ^-assoc ⟩
    (a ^ (b * c) * a ^ b) ⦃ _ ⦄ ≈˘⟨ ^-distrib ⟩
    a ^ (b * c + b)             ≈⟨ refl ⟩
    a ^ (b * suc c)             ∎ where open SubTreeReasoning
  ^-assoc {c = lim f} = limExt ⦃ ^-pres< it ⦄ ⦃ ^-pres< (*-pres< it) ⦄ λ _ → ^-assoc
```

```agda
^-infl< : ⦃ NonTrivial b ⦄ → (_^ b) inflates _<_ within NonTrivial
^-infl< {b} {x} =               begin-strict
  x                             ≈˘⟨ ^-idʳ ⟩
  x ^ 1                         <⟨ ^-pres< nt-elim ⟩
  x ^ b                         ∎ where open SubTreeReasoning
```

```agda
_^^_ : (a b : Ord) → ⦃ NonTrivial a ⦄ → Ord
^^-nt : ⦃ _ : NonTrivial a ⦄ → NonTrivial (a ^^ b)
^^-pres-rd : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves Road

^^-pres< : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves _<_
^^-pres< = map ^^-pres-rd
```

```agda
a ^^ zero = a
a ^^ suc b = (a ^^ b) ^ a where instance _ = ^^-nt {a} {b}
a ^^ lim f = lim (λ n → a ^^ f n) ⦃ ^^-pres< it ⦄

^^-nt {b = zero} = it
^^-nt {b = suc b} = ^-nt ⦃ ^^-nt ⦄ ⦃ nt-nz ⦄
^^-nt {b = lim f} = _

^^-pres-rd {a} {x} zero = set ^-infl< where instance _ = ^^-nt {a} {x}
^^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ b                        <⟨ set ^-infl< ⟩
  (a ^^ b ^ a) ⦃ _ ⦄            ≈⟨ refl ⟩
  a ^^ suc b                    ∎ where open RoadReasoning; instance _ = ^^-nt {a} {b}
^^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ f n                      <⟨ set $ f<l ⦃ ^^-pres< it ⦄ ⟩
  a ^^ lim f                    ∎ where open RoadReasoning
```
