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

## 序数函数

我们先定义序数函数的一些性质.

**定义 2-2-0** 我们说一个序数函数 $F$ **膨胀**一个序数关系 $\sim$, 当且仅当对任意序数 $x$ 都有 $x \sim F(x)$.

```agda
_inflates_ : Func → Rel → Type
F inflates _~_ = ∀ {x} → x ~ F x
```

**事实 2-1-1** 如果 $F$ 膨胀 $\lt$, 那么 $F$ 膨胀 $\leq$.

```agda
infl<→infl≤ : F inflates _<_ → F inflates _≤_
infl<→infl≤ p = <→≤ p
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

## 一些约定

**约定 2-2-x** 我们将 $\text{suc}(\text{suc}(a))$ 记作 $a^{++}$.

```agda
pattern 2+ a = suc (suc a)
```

**约定 2-2-x** 非零序数指不等于零的序数.

```agda
nonZero : Ord → Type
nonZero zero = ⊥
nonZero _ = ⊤

record NonZero (a : Ord) : Type where
  field .wrap : nonZero a
```

```agda
nz-intro-rd : Road 0 a → NonZero a
nz-intro-rd {suc _} _ = _
nz-intro-rd {lim _} _ = _

nz-intro : 0 < a → NonZero a
nz-intro = nz-intro-rd ∘ set
```

```agda
nz-elim : ⦃ NonZero a ⦄ → 0 < a
nz-elim {suc a} = z<s
nz-elim {lim f} = z<l
```

**约定 2-2-x** 非平凡序数指不等于零和一的序数.

```agda
nonTrivial : Ord → Type
nonTrivial zero       = ⊥
nonTrivial (suc zero) = ⊥
nonTrivial _          = ⊤

record NonTrivial (a : Ord) : Type where
  field .wrap : nonTrivial a
```

```agda
nt-intro-rd : Road 1 a → NonTrivial a
nt-intro-rd {suc zero} (suc ())
nt-intro-rd {2+ a}         _ = _
nt-intro-rd {suc (lim _)}  _ = _
nt-intro-rd {lim _}        _ = _

nt-intro : 1 < a → NonTrivial a
nt-intro = nt-intro-rd ∘ set
```

```agda
nt-elim : ⦃ NonTrivial a ⦄ → 1 < a
nt-elim {2+ _}        = s<s z<s
nt-elim {suc (lim _)} = s<s z<l
nt-elim {lim f}       = map lim (n<fs f 1)
```

**事实 2-2-x** 后继序数和极限序数都是非零序数; 极限序数都是非平凡序数; 非平凡序数都是非零序数.

```agda
instance
  suc-nz : NonZero (suc a)
  suc-nz = _
  lim-nz : ⦃ _ : wf f ⦄ → NonZero (lim f)
  lim-nz = _
  lim-nt : ⦃ _ : wf f ⦄ → NonTrivial (lim f)
  lim-nt = _

nt-nz : ⦃ NonTrivial a ⦄ → NonZero a
nt-nz {2+ a} = _
nt-nz {suc (lim f)} = _
nt-nz {lim f} = _
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
+-pres-rd (lim r) = lim ⦃ _ ⦄ (+-pres-rd r)
```

```agda
+-idʳ : a + 0 ≡ a
+-idʳ = refl
```

```agda
+-idˡ : 0 + a ≡ a
+-idˡ {(zero)} = refl
+-idˡ {suc a} = cong suc +-idˡ
+-idˡ {lim f} = limExt λ _ → +-idˡ
```

```agda
+-assoc : a + (b + c) ≡ (a + b) + c
+-assoc {c = zero} = refl
+-assoc {c = suc _} = cong suc +-assoc
+-assoc {c = lim _} = limExt λ _ → +-assoc
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
  x + f 0                 <⟨ f<l ⟩
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
  x + f 0                 <⟨ f<l ⟩
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
  a * f n                 <⟨ f<l-rd ⟩
  a * lim f               ∎ where open RoadReasoning
```

```agda
*-congˡ : {nza : NonZero a} {nzb : NonZero b} → a ≡ b → (a * c) ⦃ nza ⦄ ≡ (b * c) ⦃ nzb ⦄
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
*-idˡ {lim f} = limExt λ _ → *-idˡ
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
*-distrib {c = lim _} = limExt λ _ → *-distrib
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
  *-assoc {c = lim _} = limExt λ _ → *-assoc
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
a ^ suc b = (a ^ b * a) ⦃ ^-nz ⦄
a ^ lim f = lim (λ n → a ^ f n) ⦃ ^-pres< it ⦄

^-nz {b = zero} = _
^-nz {b = suc b} = *-nz ⦃ _ ⦄ ⦃ nt-nz ⦄
^-nz {b = lim f} = _

^-pres-rd zero = set *-infl< where instance _ = ^-nz
^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ b                   <⟨ set *-infl< ⟩
  a ^ b * a               ∎ where open RoadReasoning; instance _ = ^-nz
^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ f n                 <⟨ f<l-rd ⟩
  a ^ lim f               ∎ where open RoadReasoning
```

```agda
^-congˡ : {nta : NonTrivial a} {ntb : NonTrivial b} → a ≡ b → (a ^ c) ⦃ nta ⦄ ≡ (b ^ c) ⦃ ntb ⦄
^-congˡ refl = refl
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
    a ^ (b + c) * a             ≈⟨ *-congˡ ^-distrib ⟩
    (a ^ b * a ^ c * a) ⦃ _ ⦄   ≈˘⟨ *-assoc ⟩
    a ^ b * (a ^ c * a)         ≈⟨ refl ⟩
    a ^ b * (a ^ suc c)         ∎ where open SubTreeReasoning
  ^-distrib {c = lim _} = limExt λ _ → ^-distrib
```

```agda
^-nt : ⦃ nta : NonTrivial a ⦄ ⦃ nzb : NonZero b ⦄ → NonTrivial (a ^ b)
^-nt {suc a} {suc b} ⦃ nzb ⦄ =  nt-intro $ begin-strict
  1                             ≈⟨ refl ⟩
  suc a ^ 0                     ≤⟨ pres<→pres≤ ^-pres< $ <s→≤ (nz-elim ⦃ _ ⦄) ⟩
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
    ((a ^ b) ^ c * a ^ b) ⦃ _ ⦄ ≈⟨ *-congˡ ^-assoc ⟩
    (a ^ (b * c) * a ^ b) ⦃ _ ⦄ ≈˘⟨ ^-distrib ⟩
    a ^ (b * c + b)             ≈⟨ refl ⟩
    a ^ (b * suc c)             ∎ where open SubTreeReasoning
  ^-assoc {c = lim f} = limExt λ _ → ^-assoc
```

```agda
^-infl< : ⦃ NonTrivial b ⦄ → (_^ b) inflates _<_ within NonTrivial
^-infl< {b} {x} =               begin-strict
  x                             ≈˘⟨ ^-idʳ ⟩
  x ^ 1                         <⟨ ^-pres< nt-elim ⟩
  x ^ b                         ∎ where open SubTreeReasoning
```

## 伪迭代幂次

```agda
_^^_ : (a b : Ord) → ⦃ NonTrivial a ⦄ → Ord
^^-nt : ⦃ _ : NonTrivial a ⦄ → NonTrivial (a ^^ b)
^^-pres-rd : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves Road

^^-pres< : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves _<_
^^-pres< = map ^^-pres-rd
```

```agda
a ^^ zero = a
a ^^ suc b = ((a ^^ b) ^ a) ⦃ ^^-nt ⦄
a ^^ lim f = lim (λ n → a ^^ f n) ⦃ ^^-pres< it ⦄

^^-nt {b = zero} = it
^^-nt {b = suc b} = ^-nt ⦃ _ ⦄ ⦃ nt-nz ⦄
^^-nt {b = lim f} = _

^^-pres-rd {a} {x} zero = set ^-infl< where instance _ = ^^-nt {a} {x}
^^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ b                        <⟨ set ^-infl< ⟩
  (a ^^ b ^ a) ⦃ _ ⦄            ≈⟨ refl ⟩
  a ^^ suc b                    ∎ where open RoadReasoning; instance _ = ^^-nt {a} {b}
^^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ f n                      <⟨ f<l-rd ⟩
  a ^^ lim f                    ∎ where open RoadReasoning
```

```agda
^^-fake : ⦃ _ : NonTrivial a ⦄ → a ^^ b ≡ a ^ (a ^ b)
^^-fake {a} {b = zero}  = sym *-idˡ
^^-fake {a} {b = suc b} =       begin-equality
  a ^^ suc b                    ≈⟨ refl ⟩
  ((a ^^ b) ^ a) ⦃ _ ⦄          ≈⟨ ^-congˡ ^^-fake ⟩
  ((a ^ (a ^ b)) ^ a) ⦃ _ ⦄     ≈⟨ ^-assoc ⟩
  a ^ (a ^ b * a) ⦃ _ ⦄         ≈⟨ refl ⟩
  a ^ (a ^ suc b)               ∎ where open SubTreeReasoning; instance _ = ^-nz
^^-fake {a} {b = lim f} = limExt λ _ → ^^-fake
```
  