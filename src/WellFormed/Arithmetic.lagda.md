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
syntax restricted-infl-syntax F _~_ = F inflatesᴿ _~_
```

```agda
restricted-pres-syntax : {P : Ord → Type} → Func↾ P → Rel → Type
restricted-pres-syntax {P} F _~_ = ∀ {x y} ⦃ p₁ : P x ⦄ ⦃ p₂ : P y ⦄ → x ~ y → F x ~ F y
syntax restricted-pres-syntax F _~_ = F preservesᴿ _~_
```

```agda
record Infl↾ (P : Ord → Type) : Type where
  constructor mkInfl↾
  field
    _[_] : Func↾ P
    infl< : _[_] inflatesᴿ _<_

  infl-rd : _[_] inflatesᴿ Road
  infl-rd = set infl<
open Infl↾ public
```

**定义 2-2-x** 我们说一个保持 $\lt$ 的序数函数 $F$ 是**连续**的, 当且仅当对任意良构序列 $f$ 都有 $F(\lim f) = \lim (F \circ f)$.

```agda
continuous : F preserves _<_ → Type
continuous {F} pres = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘ f) ⦃ pres it ⦄
```

**注意 2-2-x** 在传统定义中「保持 $\lt$」与「连续」分开的, 但在我们这套定义中只有保持 $\lt$ 的函数才可以谈论是否连续, 因为受良构条件约束.

**定义 2-1-x** 我们说一个序数函数 $F$ 是**正规**的, 当且仅当它保持 $\lt$ 且连续.

```agda
record Normal : Type where
  constructor mkNormal
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<
open Normal public
```

```agda
private variable
  i j : Ord
  ℱ : Infl↾ (i ≤_)
```

```agda
_^⟨_⟩_ : (ℱ : Infl↾ (i ≤_)) → Ord → Func↾ (i ≤_)
^⟨⟩*-infl≤ : (_^⟨_⟩_ ℱ a) inflatesᴿ _≤_
^⟨*⟩-pres-rd : {ℱ : Infl↾ (i ≤_)} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves Road
```

```agda
^⟨*⟩-pres< : {ℱ : Infl↾ (i ≤_)} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves _<_
^⟨*⟩-pres< = map ^⟨*⟩-pres-rd

^⟨*⟩-pres≤ : {ℱ : Infl↾ (i ≤_)} ⦃ _ : i ≤ j ⦄ → (ℱ ^⟨_⟩ j) preserves _≤_
^⟨*⟩-pres≤ = pres<→pres≤ ^⟨*⟩-pres<
```

```agda
init≤ : {ℱ : Infl↾ (i ≤_)} ⦃ _ : i ≤ j ⦄ → i ≤ ℱ ^⟨ a ⟩ j
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
_⟨_⟩^ : (ℱ : Infl↾ (i ≤_)) (j : Ord ) → ⦃ i ≤ j ⦄ → Normal
ℱ ⟨ j ⟩^ = mkNormal (ℱ ^⟨_⟩ j) ^⟨*⟩-pres< refl
```

```agda
^⟨⟩*-infl< : ⦃ NonZero a ⦄ → (_^⟨_⟩_ ℱ a) inflatesᴿ _<_
^⟨⟩*-infl< {suc a} {ℱ} {x} =              begin-strict
  x                                       ≤⟨ ^⟨⟩*-infl≤ ⟩
  ℱ ^⟨ a ⟩ x                              <⟨ ^⟨*⟩-pres< zero₁ ⟩
  ℱ ^⟨ suc a ⟩ x                          ∎ where open SubTreeReasoning
^⟨⟩*-infl< {lim f} {ℱ} {x} =              begin-strict
  x                                       <⟨ ^⟨⟩*-infl< ⦃ nz-intro (z<fs f 0) ⦄ ⟩
  ℱ ^⟨ f 1 ⟩ x                            <⟨ ^⟨*⟩-pres< f<l ⟩
  ℱ ^⟨ lim f ⟩ x                          ∎ where open SubTreeReasoning
```

```agda
_^⟨_⟩ : (ℱ : Infl↾ (i ≤_)) (a : Ord) → ⦃ NonZero a ⦄ → Infl↾ (i ≤_)
_^⟨_⟩ ℱ a = mkInfl↾ (_^⟨_⟩_ ℱ a) ^⟨⟩*-infl<
```

```agda
private
  pres = ^⟨*⟩-pres<
  pres≤ = ^⟨*⟩-pres≤
  instance
    _ = z≤
    _ = ≤-refl
    _ : NonZero (suc a)
    _ = _
    _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
    _ = _
    _ : NonTrivial ω
    _ = _
```

## 加法

```agda
Suc : Infl↾ (0 ≤_)
Suc = mkInfl↾ (λ x → suc x) zero₁
```

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
a + b = Suc ^⟨ b ⟩ a
```

```agda
LeftAdd : (a : Ord) → Normal
LeftAdd a = mkNormal (a +_) pres refl
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
+-idˡ (lim f) = limExt ⦃ pres it ⦄ (+-idˡ ∘ f)
```

## 乘法

```agda
RightAdd : (b : Ord) → ⦃ NonZero b ⦄ → Infl↾ (0 ≤_)
RightAdd b = Suc ^⟨ b ⟩
```

```agda
_⋅_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 7 _⋅_
a ⋅ b = (RightAdd a) ^⟨ b ⟩ 0
```

```agda
LeftMul : (a : Ord) → ⦃ NonZero a ⦄ → Normal
LeftMul a = mkNormal (a ⋅_) pres refl
```

```agda
⋅-idʳ : ∀ a → ⦃ _ : NonZero a ⦄ → a ⋅ 1 ≡ a
⋅-idʳ a =     begin-equality
  a ⋅ 1       ≈⟨ refl ⟩
  a ⋅ 0 + a   ≈⟨ cong (_+ a) refl ⟩
  0 + a       ≈⟨ +-idˡ a ⟩
  a           ∎ where open SubTreeReasoning
```

```agda
⋅-idˡ : ∀ a → 1 ⋅ a ≡ a
⋅-idˡ zero = refl
⋅-idˡ (suc a) = cong suc (⋅-idˡ a)
⋅-idˡ (lim f) = limExt ⦃ pres it ⦄ (⋅-idˡ ∘ f)
```

```agda
⋅-2 : ∀ a → ⦃ _ : NonZero a ⦄ → a ⋅ 2 ≡ a + a
⋅-2 a =                           begin-equality
  a ⋅ 2                           ≈⟨ refl ⟩
  (Suc ^⟨ a ⟩ (a ⋅ 1)) ⦃ init≤ ⦄  ≈⟨ cong (λ p → (Suc ^⟨ a ⟩ (a ⋅ 1)) ⦃ p ⦄) (pathToEq (isProp≤ _ _)) ⟩
  (Suc ^⟨ a ⟩ (a ⋅ 1)) ⦃ z≤ ⦄     ≈⟨ refl ⟩
  a ⋅ 1 + a                       ≈⟨ cong (_+ a) (⋅-idʳ a) ⟩
  a + a                           ∎ where open SubTreeReasoning
```

## 幂

```agda
RightMul : (b : Ord) → ⦃ NonTrivial b ⦄ → Infl↾ (1 ≤_)
RightMul b = mkInfl↾ _⋅b infl where
  instance _ : ⦃ 1 ≤ a ⦄ → NonZero a
  _ = nz-intro (s≤→< it)
  _⋅b : Func↾ (1 ≤_)
  (x ⋅b) = x ⋅ b
  infl : _⋅b inflatesᴿ _<_
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
^-idʳ : ∀ a → ⦃ _ : NonTrivial a ⦄ → a ^ 1 ≡ a
^-idʳ a =     begin-equality
  a ^ 1       ≈⟨ refl ⟩
  a ^ 0 ⋅ a   ≈⟨ refl ⟩
  1 ⋅ a       ≈⟨ ⋅-idˡ a ⟩
  a           ∎ where open SubTreeReasoning
```

```agda
Base : (a : Ord) → ⦃ NonTrivial a ⦄ → Normal
Base a = mkNormal (a ^_) pres refl
```

```agda
ω^ : Normal
ω^ = Base ω
```

```agda
ω^a>0 : 0 < ω^ [ a ]
ω^a>0 {a} =   begin-strict
  0           <⟨ zero₁ ⟩
  1           ≈⟨ refl ⟩
  ω ^ 0       ≤⟨ pres≤ z≤ ⟩
  ω^ [ a ]    ∎ where open SubTreeReasoning
```

```agda
instance
  ω^a-nz : NonZero (ω^ [ a ])
  ω^a-nz = nz-intro ω^a>0
```

```agda
ω^↾<ω-infl< : ((ω^ [_]) ↾ (_< ω)) inflatesᴿ _<_
ω^↾<ω-infl< {(zero)} = zero₁
ω^↾<ω-infl< {suc x} =   begin-strict
  suc x                 <⟨ s<s (ω^↾<ω-infl< ⦃ <-trans zero₁ it ⦄) ⟩
  suc (ω^ [ x ])        ≈⟨ refl ⟩
  ω^ [ x ] + 1          ≤⟨ pres≤ (<→s≤ ω^a>0) ⟩
  ω^ [ x ] + ω^ [ x ]   ≈˘⟨ ⋅-2 _ ⟩
  ω^ [ x ] ⋅ 2          <⟨ pres (f<l {n = 2}) ⟩
  ω^ [ x ] ⋅ ω          ≈⟨ refl ⟩
  ω^ [ suc x ]          ∎ where open SubTreeReasoning
ω^↾<ω-infl< {lim _} ⦃ p ⦄ = ⊥-elim $ l≮ω p
```
