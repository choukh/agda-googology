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

## 可迭代函数

```agda
Func↾ : Ord → Type
Func↾ i = (x : Ord) ⦃ i≤ : i ≤ x ⦄ → Ord
```

```agda
inflates-from-syntax : (i : Ord) → Func↾ i → Rel → Type
inflates-from-syntax i F _~_ = ∀ {x} ⦃ i≤ : i ≤ x ⦄ → x ~ F x
syntax inflates-from-syntax i F _~_ = F inflates _~_ from i

preserves-from-syntax : (i : Ord) → Func↾ i → Rel → Type
preserves-from-syntax i F _~_ = ∀ {x y} ⦃ i≤₁ : i ≤ x ⦄ ⦃ i≤₂ : i ≤ y ⦄ → x ~ y → F x ~ F y
syntax preserves-from-syntax i F _~_ = F preserves _~_ from i
```

```agda
record EverInfl (init : Ord) : Type where
  constructor everInfl
  field
    _[_] : Func↾ init
    infl< : _[_] inflates _<_ from init

  infl-rd : _[_] inflates Road from init
  infl-rd = set infl<

variable
  i j : Ord
  ℱ : EverInfl i

open EverInfl public
open Normal public
```

```agda
_^⟨_⟩_ : (ℱ : EverInfl i) → Ord → Func↾ i
^⟨⟩*-infl≤ : (_^⟨_⟩_ ℱ a) inflates _≤_ from i
^⟨*⟩-pres-rd : {ℱ : EverInfl i} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves Road

^⟨*⟩-pres< : {ℱ : EverInfl i} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves _<_
^⟨*⟩-pres< = map ^⟨*⟩-pres-rd
```

```agda
init≤ : {ℱ : EverInfl i} ⦃ _ : i ≤ j ⦄ → i ≤ ℱ ^⟨ a ⟩ j
init≤ {i} {j} {a} {ℱ} =                   begin
  i                                       ≤⟨ it ⟩
  j                                       ≤⟨ ^⟨⟩*-infl≤ ⟩
  ℱ ^⟨ a ⟩ j                              ∎ where open SubTreeReasoning
```

```agda
ℱ ^⟨ zero ⟩ j = j
ℱ ^⟨ suc a ⟩ j = (ℱ [ ℱ ^⟨ a ⟩ j ]) ⦃ init≤ ⦄
ℱ ^⟨ lim f ⟩ j = lim (λ n → ℱ ^⟨ f n ⟩ j) ⦃ ^⟨*⟩-pres< it ⦄
```

```agda
^⟨⟩*-infl≤ {ℱ} {a = zero} = inr refl
^⟨⟩*-infl≤ {ℱ} {a = suc a} {x} =          begin
  x                                       ≤⟨ ^⟨⟩*-infl≤ ⟩
  ℱ ^⟨ a ⟩ x                              ≤⟨ <→≤ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc a ⟩ x                          ∎ where open SubTreeReasoning
^⟨⟩*-infl≤ {ℱ} {a = lim f} {x} =          begin
  x                                       ≤⟨ ^⟨⟩*-infl≤ ⟩
  ℱ ^⟨ f 0 ⟩ x                            <⟨ map (lim ⦃ ^⟨*⟩-pres< it ⦄) (^⟨*⟩-pres< it) ⟩
  ℱ ^⟨ lim f ⟩ x                          ∎ where open SubTreeReasoning
```

```agda
^⟨*⟩-pres-rd {j} {ℱ} {x} zero =           begin-strict
  ℱ ^⟨ x ⟩ j                              <⟨ infl-rd ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc x ⟩ j                          ∎ where open RoadReasoning
^⟨*⟩-pres-rd {j} {ℱ} {x} (suc {b} r) =    begin-strict
  ℱ ^⟨ x ⟩ j                              <⟨ ^⟨*⟩-pres-rd r ⟩
  ℱ ^⟨ b ⟩ j                              <⟨ infl-rd ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc b ⟩ j                          ∎ where open RoadReasoning
^⟨*⟩-pres-rd {j} {ℱ} {x} (lim {f} {n} r) = begin-strict
  ℱ ^⟨ x ⟩ j                              <⟨ ^⟨*⟩-pres-rd r ⟩
  ℱ ^⟨ f n ⟩ j                            <⟨ lim ⦃ ^⟨*⟩-pres< it ⦄ (^⟨*⟩-pres-rd (set it)) ⟩
  ℱ ^⟨ lim f ⟩ j                          ∎ where open RoadReasoning
```

```agda
^⟨*⟩-pres≤ : {ℱ : EverInfl i} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves _≤_
^⟨*⟩-pres≤ = pres<→pres≤ ^⟨*⟩-pres<
```

```agda
^⟨⟩*-infl< : ⦃ NonZero a ⦄ → (_^⟨_⟩_ ℱ a) inflates _<_ from i
^⟨⟩*-infl< {suc a} {ℱ} {x} =              begin-strict
  x                                       ≤⟨ ^⟨⟩*-infl≤ ⟩
  ℱ ^⟨ a ⟩ x                              <⟨ ^⟨*⟩-pres< zero₁ ⟩
  ℱ ^⟨ suc a ⟩ x                          ∎ where open SubTreeReasoning
^⟨⟩*-infl< {lim f} {ℱ} {x} =              begin-strict
  x                                       <⟨ ^⟨⟩*-infl< ⦃ nz-intro (z<fs f) ⦄ ⟩
  ℱ ^⟨ f 1 ⟩ x                            <⟨ ^⟨*⟩-pres< f<l ⟩
  ℱ ^⟨ lim f ⟩ x                          ∎ where open SubTreeReasoning
```

```agda
_^⟨_⟩ : (ℱ : EverInfl i) (a : Ord) → ⦃ NonZero a ⦄ → EverInfl i
_^⟨_⟩ ℱ a = everInfl (_^⟨_⟩_ ℱ a) ^⟨⟩*-infl<
```

```agda
_⟨_⟩^ : (ℱ : EverInfl i) (j : Ord ) → ⦃ i ≤ j ⦄ → Normal
ℱ ⟨ j ⟩^ = normal (ℱ ^⟨_⟩ j) ^⟨*⟩-pres< refl
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
