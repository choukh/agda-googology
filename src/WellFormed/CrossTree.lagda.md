---
title: 形式化大数数学 (2.3 - 跨树关系)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.3 - 跨树关系)

> 交流Q群: 893531731  
> 本文源码: [CrossTree.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/CrossTree.lagda.md)  
> 高亮渲染: [CrossTree.html](https://choukh.github.io/agda-googology/WellFormed.CrossTree.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.CrossTree where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic

open import Relation.Binary.Definitions
open import Induction.WellFounded
```

## 非严格序

**定义 2-3-x**

```agda
infix 6 _≼_
data _≼_ : Rel where
  z≼  : 0 ≼ a
  s≼s : a ≼ b → suc a ≼ suc b
  ≼l  : {w : wf f} → a ≼ f n → a ≼ lim f ⦃ w ⦄
  l≼  : {w : wf f} → (∀ {n} → f n ≼ a) → lim f ⦃ w ⦄ ≼ a
```

**事实 2-3-x**

```agda
s≼s-inj : suc injects _≼_
s≼s-inj (s≼s p) = p
```

**事实 2-3-x**

```agda
l≼l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≼ g n) → lim f ⦃ wff ⦄ ≼ lim g ⦃ wfg ⦄
l≼l p = l≼ (≼l p)
```

**事实 2-3-x**

```agda
l≼ls : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≼ g (suc n)) → lim f ⦃ wff ⦄ ≼ lim g ⦃ wfg ⦄
l≼ls p = l≼ (λ {n} → (≼l {n = suc n} p))
```

**定理 2-3-x**

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc x} = s≼s ≼-refl
≼-refl {lim f} = l≼ (≼l ≼-refl)
```

**推论 2-3-x**

```agda
f≼l : {w : wf f} → f n ≼ lim f ⦃ w ⦄
f≼l = ≼l ≼-refl
```

**定理 2-3-x**

```agda
≼-trans : Transitive _≼_
≼-trans z≼      q       = z≼
≼-trans (s≼s p) (s≼s q) = s≼s (≼-trans p q)
≼-trans p       (≼l q)  = ≼l (≼-trans p q)
≼-trans (l≼ p)  q       = l≼ (≼-trans p q)
≼-trans (≼l p)  (l≼ q)  = ≼-trans p q
```

**推论 2-3-x**

```agda
l≼-inv : {w : wf f} → lim f ⦃ w ⦄ ≼ a → f n ≼ a
l≼-inv (≼l p) = ≼-trans f≼l (≼l p)
l≼-inv (l≼ p) = p
```

**引理 2-3-x**

```agda
≼-suc : a ≼ b → a ≼ suc b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l p) = ≼-trans (≼-suc p) (s≼s f≼l)
≼-suc (l≼ p) = l≼ (≼-suc p)

≼-zero : a ≼ suc a
≼-zero = ≼-suc ≼-refl
```

**定理 2-3-x**

```agda
≤→≼-rd : NSRoad a b → a ≼ b
≤→≼-rd (inl zero) = ≼-suc ≼-refl
≤→≼-rd (inl (suc r)) = ≼-suc (≤→≼-rd (inl r))
≤→≼-rd (inl (lim r)) = ≼l (≤→≼-rd (inl r))
≤→≼-rd (inr refl) = ≼-refl

≤→≼ : a ≤ b → a ≼ b
≤→≼ (inl r) = ≤→≼-rd (inl (set r))
≤→≼ (inr refl) = ≼-refl
```

## 外延相等

**定义 2-3-x**

```agda
_≈_ : Rel; infix 5 _≈_
a ≈ b = a ≼ b × b ≼ a
```

**事实 2-3-x**

```agda
≼-antisym : Antisymmetric _≈_ _≼_
≼-antisym p q = p , q
```

**定理 2-3-x**

```agda
≈-refl : Reflexive _≈_
≈-refl = ≼-refl , ≼-refl

≈-sym : Symmetric _≈_
≈-sym (p , q) = q , p

≈-trans : Transitive _≈_
≈-trans (p , q) (u , v) = ≼-trans p u , ≼-trans v q
```

```agda
≡→≈ : a ≡ b → a ≈ b
≡→≈ refl = ≈-refl
```

**事实 2-3-x**

```agda
s≈s : a ≈ b → suc a ≈ suc b
s≈s (p , q) = s≼s p , s≼s q

s≈s-inj : suc injects _≈_
s≈s-inj (p , q) = s≼s-inj p , s≼s-inj q
```

**事实 2-3-x**

```agda
l≈l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≈ g n) → lim f ⦃ wff ⦄ ≈ lim g ⦃ wfg ⦄
l≈l p = l≼l (fst p) , l≼l (snd p)
```

**事实 2-3-x**

```agda
l≈ls : {w : wf f} {ws : wf (f ∘ suc)} → f 0 ≼ f 1 → lim f ⦃ w ⦄ ≈ lim (f ∘ ℕ.suc) ⦃ ws ⦄
l≈ls p = l≼ (λ { {(zero)} → ≼l p ; {suc n} → f≼l }) , l≼ f≼l
```

## 严格序

```agda
_≺_ _⋠_ _⊀_ : Rel; infix 6 _≺_ _⋠_ _⊀_
a ≺ b = suc a ≼ b 
a ⋠ b = a ≼ b → ⊥
a ⊀ b = a ≺ b → ⊥
```

```agda
≺→≼ : a ≺ b → a ≼ b
≺→≼ (s≼s p) = ≼-suc p
≺→≼ (≼l p) = ≼l (≼-trans ≼-zero p)
```

```agda
≺-zero : a ≺ suc a
≺-zero = s≼s ≼-refl

≺-suc : a ≺ b → a ≺ suc b
≺-suc p = s≼s (≺→≼ p)
```

```agda
<→≺-rd : Road a b → a ≺ b
<→≺-rd zero = ≺-zero
<→≺-rd (suc r) = ≺-suc (<→≺-rd r)
<→≺-rd (lim r) = ≼l (≤→≼-rd (<→s≤-rd r))

<→≺ : a < b → a ≺ b
<→≺ r = <→≺-rd (set r)
```

```agda
z≺s : 0 ≺ suc a
z≺s = s≼s z≼
```

```agda
≼→≺s : a ≼ b → a ≺ suc b
≼→≺s z≼ = z≺s
≼→≺s (s≼s p) = s≼s (s≼s p)
≼→≺s (≼l p) = s≼s (≼l p)
≼→≺s (l≼ p) = s≼s (l≼ p)
```

```agda
≺s→≼ : a ≺ suc b → a ≼ b
≺s→≼ p = s≼s-inj p
```

```agda
s⋠ : suc a ⋠ a
l⋠f : {w : wf f} → lim f ⦃ w ⦄ ⋠ f n
l⋠f p = s⋠ (≼-trans (≤→≼ (<→s≤ f<l)) p)

s⋠ {suc a} p = s⋠ (s≼s-inj p)
s⋠ {lim f} (≼l p) = l⋠f (≼-trans ≼-zero p)
```

```agda
≺-irrefl : Irreflexive _≈_ _≺_
≺-irrefl (_ , p) q = s⋠ (≼-trans q p)

≺-trans : Transitive _≺_
≺-trans p q = ≼-trans p (≺→≼ q)

≺-asym : Asymmetric _≺_
≺-asym p q = ≺-irrefl ≈-refl (≺-trans p q)
```

```agda
≺-≼-trans : Trans _≺_ _≼_ _≺_
≺-≼-trans p q = ≼-trans p q

≼-≺-trans : Trans _≼_ _≺_ _≺_
≼-≺-trans p q = ≼-trans (s≼s p) q

≺-resp-≈ : _≺_ Respects₂ _≈_
≺-resp-≈ = (λ { (p , q) u → ≺-≼-trans u p })
         , (λ { (p , q) u → ≼-≺-trans q u })
```

```agda
≺-acc : a ≼ b → Acc _≺_ b → Acc _≺_ a
≺-acc p (acc r) = acc (λ q → r (≺-≼-trans q p))
```

```agda
≺-wfnd : WellFounded _≺_
≺-wfnd zero    = acc λ ()
≺-wfnd (suc a) = acc λ { (s≼s p) → ≺-acc p (≺-wfnd a) }
≺-wfnd (lim f) = acc λ { (≼l p) → ≺-acc (≺→≼ p) (≺-wfnd (f _)) }
```

## 结构实例化

```agda
open import Relation.Binary.Structures {A = Ord} _≈_
```

```agda
≈-isEquivalence : IsEquivalence
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans }
```

```agda
≼-isPreorder : IsPreorder _≼_
≼-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = fst
  ; trans = ≼-trans }

≼-isPartialOrder : IsPartialOrder _≼_
≼-isPartialOrder = record { isPreorder = ≼-isPreorder ; antisym = ≼-antisym }
```

```agda
≺-isStrictPartialOrder : IsStrictPartialOrder _≺_
≺-isStrictPartialOrder = record
  { isEquivalence = ≈-isEquivalence
  ; irrefl = ≺-irrefl
  ; trans = ≺-trans
  ; <-resp-≈ = ≺-resp-≈ }
```

```agda
module CrossTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≈_} {_≤_ = _≼_} {_<_ = _≺_}
    ≼-isPreorder ≺-asym ≺-trans ≺-resp-≈ ≺→≼ ≺-≼-trans ≼-≺-trans
    public
```

## 跨树算术定理

### 加法

```agda
+a-infl≼ : (_+ a) inflates _≼_
+a-infl≼ = ≤→≼ +-infl≤

+a-infl≺ : ⦃ NonZero a ⦄ → (_+ a) inflates _≺_
+a-infl≺ = <→≺ +-infl
```

```agda
a+-infl≼ : (a +_) inflates _≼_
a+-infl≼ {x = zero}  = z≼
a+-infl≼ {x = suc x} = s≼s a+-infl≼
a+-infl≼ {x = lim f} = l≼l a+-infl≼
```

```agda
1+l-absorb : {w : wf f} → 1 + lim f ⦃ w ⦄ ≈ lim f ⦃ w ⦄
1+l-absorb {f} {w} = l≼ls (aux (<→≺ w)) , l≼l a+-infl≼ where
  aux : a ≺ b → 1 + a ≼ b
  aux {(zero)} (s≼s p) = z≺s
  aux {suc a} (s≼s p)  = s≼s (aux p)
  aux {lim f} (s≼s p)  = l≼ (aux (s≼s (≼-trans f≼l p)))
  aux (≼l p) = ≼l (aux p)
```

```agda
a+-pres≼ : (a +_) preserves _≼_
a+-pres≼ z≼       = +a-infl≼
a+-pres≼ (s≼s p)  = s≼s (a+-pres≼ p)
a+-pres≼ (≼l p)   = ≼l (a+-pres≼ p)
a+-pres≼ (l≼ p)   = l≼ (a+-pres≼ p)
```

```agda
a+-pres≺ : (a +_) preserves _≺_
a+-pres≺ (s≼s p) = s≼s (a+-pres≼ p)
a+-pres≺ (≼l p)  = ≼l (a+-pres≼ p)
```

```agda
+a-pres≼ : (_+ a) preserves _≼_
+a-pres≼ {(zero)} p = p
+a-pres≼ {suc a} p  = s≼s (+a-pres≼ p)
+a-pres≼ {lim f} p  = l≼l (+a-pres≼ p)
```

```agda
+-pres≼ : a ≼ b → c ≼ d → a + c ≼ b + d
+-pres≼ {a} {b} {c} {d} p q = begin
  a + c                     ≤⟨ a+-pres≼ q ⟩
  a + d                     ≤⟨ +a-pres≼ p ⟩
  b + d                     ∎ where open CrossTreeReasoning
```

```agda
a+-cong≈ : b ≈ c → a + b ≈ a + c
a+-cong≈ (p , q) = a+-pres≼ p , a+-pres≼ q

+a-cong≈ : b ≈ c → b + a ≈ c + a
+a-cong≈ (p , q) = +a-pres≼ p , +a-pres≼ q
```

### 乘法

```agda
a*-pres≼ : ⦃ _ : NonZero a ⦄ → (a *_) preserves _≼_
a*-pres≼ z≼       = z≼
a*-pres≼ (s≼s p)  = +a-pres≼ (a*-pres≼ p)
a*-pres≼ (≼l p)   = ≼l (a*-pres≼ p)
a*-pres≼ (l≼ p)   = l≼ (a*-pres≼ p)
```

```agda
*a-infl≼ : ⦃ NonZero a ⦄ → (_* a) inflates _≼_ within NonZero
*a-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ a*-id ⟩
  x * 1                     ≤⟨ a*-pres≼ (<→≺ nz-elim) ⟩
  x * a                     ∎ where open CrossTreeReasoning
```

```agda
a*-pres≺ : ⦃ _ : NonZero a ⦄ → (a *_) preserves _≺_
a*-pres≺ {a} {x} (s≼s {b} p) = begin-strict
  a * x                     <⟨ +a-infl≺ ⟩
  a * x + a                 ≤⟨ +a-pres≼ (a*-pres≼ p) ⟩
  a * b + a                 ∎ where open CrossTreeReasoning
a*-pres≺ {a} {x} (≼l {f} {n} p) = begin-strict
  a * x                     <⟨ a*-pres≺ p ⟩
  a * f n                   ≤⟨ f≼l ⟩
  lim- (λ n → a * f n)      ∎ where open CrossTreeReasoning
```

```agda
*a-infl≺ : ⦃ NonTrivial a ⦄ → (_* a) inflates _≺_ within NonZero
*a-infl≺ {a} {x} =          begin-strict
  x                         ≈˘⟨ ≡→≈ a*-id ⟩
  x * 1                     <⟨ a*-pres≺ (<→≺ nt-elim) ⟩
  x * a                     ∎ where open CrossTreeReasoning
```

```agda
*a-pres≼ : (_* a) preserves _≼_ within NonZero
*a-pres≼ {(zero)} _ = ≼-refl
*a-pres≼ {lim f} p = l≼l (*a-pres≼ p)
*a-pres≼ {suc a} {x} {y} p = begin
  x * a + x                 ≤⟨ a+-pres≼ p ⟩
  x * a + y                 ≤⟨ +a-pres≼ (*a-pres≼ p) ⟩
  y * a + y                 ∎ where open CrossTreeReasoning
```

```agda
a*-infl≼ : ⦃ _ : NonZero a ⦄ → (a *_) inflates _≼_
a*-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ *a-id ⟩
  (1 * x) ⦃ _ ⦄             ≤⟨ *a-pres≼ ⦃ _ ⦄ (<→≺ nz-elim) ⟩
  a * x                     ∎ where open CrossTreeReasoning
```

```agda
a*-cong≈ : ⦃ _ : NonZero a ⦄ → b ≈ c → a * b ≈ a * c
a*-cong≈ (p , q) = a*-pres≼ p , a*-pres≼ q

*a-cong≈ : ⦃ _ : NonZero b ⦄ ⦃ _ : NonZero c ⦄ → b ≈ c → b * a ≈ c * a
*a-cong≈ (p , q) = *a-pres≼ p , *a-pres≼ q
```

## 幂运算

```agda
a^-pres≼ : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _≼_
a^-pres≼ z≼ = <→≺ nz-elim                 where instance _ = ^-nz
a^-pres≼ (s≼s p) = *a-pres≼ (a^-pres≼ p)  where instance _ = ^-nz
a^-pres≼ (≼l p) = ≼l (a^-pres≼ p)
a^-pres≼ (l≼ p) = l≼ (a^-pres≼ p)
```

```agda
^a-infl≼ : ⦃ NonZero a ⦄ → (_^ a) inflates _≼_ within NonTrivial
^a-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ a^-id ⟩
  x ^ 1                     ≤⟨ a^-pres≼ (<→≺ nz-elim) ⟩
  x ^ a                     ∎ where open CrossTreeReasoning
```

```agda
a^-pres≺ : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _≺_
a^-pres≺ {a} {x} (s≼s {b} p) = begin-strict
  a ^ x                     <⟨ *a-infl≺ ⟩
  a ^ x * a                 ≤⟨ *a-pres≼ (a^-pres≼ p) ⟩
  a ^ b * a                 ∎ where open CrossTreeReasoning; instance _ = ^-nz
a^-pres≺ {a} {x} (≼l {f} {n} p) = begin-strict
  a ^ x                     <⟨ a^-pres≺ p ⟩
  a ^ f n                   ≤⟨ f≼l ⟩
  lim- (λ n → a ^ f n)      ∎ where open CrossTreeReasoning
```

```agda
^a-infl≺ : ⦃ NonTrivial a ⦄ → (_^ a) inflates _≺_ within NonTrivial
^a-infl≺ {a} {x} =          begin-strict
  x                         ≈˘⟨ ≡→≈ a^-id ⟩
  x ^ 1                     <⟨ a^-pres≺ (<→≺ nt-elim) ⟩
  x ^ a                     ∎ where open CrossTreeReasoning
```

```agda
^a-pres≼ : (_^ a) preserves _≼_ within NonTrivial
^a-pres≼ {(zero)} _ = ≼-refl
^a-pres≼ {lim f} p = l≼l (^a-pres≼ p)
^a-pres≼ {suc a} {x} {y} p = begin
  x ^ a * x                 ≤⟨ a*-pres≼ p ⟩
  x ^ a * y                 ≤⟨ *a-pres≼ (^a-pres≼ p) ⟩
  y ^ a * y                 ∎ where open CrossTreeReasoning; instance _ = ^-nz
```

```agda
a^-infl≼ : ⦃ _ : NonTrivial a ⦄ → (a ^_) inflates _≼_
a^-infl≼ {a} {x} =          begin
  x                         ≤⟨ aux ⟩
  (2 ^ x) ⦃ _ ⦄             ≤⟨ ^a-pres≼ ⦃ _ ⦄ (<→≺ nt-elim) ⟩
  a ^ x                     ∎ where
  open CrossTreeReasoning
  instance _ : NonTrivial 2   ; _ = _
  instance _ : NonZero (2 ^ b); _ = ^-nz
  aux : b ≼ 2 ^ b
  aux {(zero)} = z≼
  aux {lim f} = l≼l aux
  aux {suc b} =             begin
    b + 1                   ≤⟨ +a-pres≼ aux ⟩
    2^b + 1                 ≤⟨ a+-pres≼ (<→≺ nz-elim) ⟩
    2^b + 2^b               ≈˘⟨ ≡→≈ (cong (_+ 2^b) +a-id) ⟩
    0 + 2^b + 2^b           ∎ where 2^b = 2 ^ b
```

```agda
a^-cong≈ : ⦃ _ : NonTrivial a ⦄ → b ≈ c → a ^ b ≈ a ^ c
a^-cong≈ (p , q) = a^-pres≼ p , a^-pres≼ q

^a-cong≈ : ⦃ _ : NonTrivial b ⦄ ⦃ _ : NonTrivial c ⦄ → b ≈ c → b ^ a ≈ c ^ a
^a-cong≈ (p , q) = ^a-pres≼ p , ^a-pres≼ q
```

```agda
+-assoc-n : ⦃ _ : NonZero a ⦄ → a + a * fin n ≡ a * fin n + a
+-assoc-n {n = zero} = sym +a-id
+-assoc-n {a} {n = suc n} = begin-equality
  a + a * suc (fin n)     ≈⟨ refl ⟩
  a + (a * fin n + a)     ≈⟨ +-assoc ⟩
  a + a * fin n + a       ≈⟨ cong (_+ a) +-assoc-n ⟩
  a * suc (fin n) + a     ∎ where open SubTreeReasoning
```

```agda
ω^-absorb : a ≺ b → ω ^ a + ω ^ b ≈ ω ^ b
ω^-absorb {a} {b = suc b} (s≼s a≼b) =
  (l≼ λ {n} →               begin
    ω ^ a + ω ^ b * fin n   ≤⟨ +a-pres≼ (a^-pres≼ a≼b) ⟩
    ω ^ b + ω ^ b * fin n   ≈⟨ ≡→≈ +-assoc-n ⟩
    ω ^ b * fin n + ω ^ b   ≈⟨ ≈-refl ⟩
    ω ^ b * suc (fin n)     ≤⟨ a*-pres≼ (<→≺ n<ω) ⟩
    ω ^ b * ω               ∎) ,
  (l≼ λ {n} →               begin
    ω ^ b * fin n           ≤⟨ a+-infl≼ ⟩
    ω ^ a + ω ^ b * fin n   ≤⟨ a+-pres≼ (a*-pres≼ $ ≤→≼ $ inl n<ω) ⟩
    ω ^ a + ω ^ b * ω       ∎) where
  open CrossTreeReasoning
  instance _ = ^-nz
ω^-absorb {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
  open CrossTreeReasoning
  import Data.Nat.Properties as ℕ
  aux : ω ^ a + ω ^ f m ≼ lim- (λ m → ω ^ f m)
  aux {m} with ℕ.<-cmp n m
  ... | tri< n<m _ _  = ≼l $ begin
    ω ^ a + ω ^ f m         ≤⟨ fst (ω^-absorb a≺fm) ⟩
    ω ^ f m                 ∎ where
    a≺fm =                  begin-strict
      a                     <⟨ a≺fn ⟩
      f n                   <⟨ <→≺ (seq-pres n<m) ⟩
      f m                   ∎
  ... | tri≈ _ refl _ = ≼l $ begin
    ω ^ a + ω ^ f n         ≤⟨ fst (ω^-absorb a≺fn) ⟩
    ω ^ f n                 ∎
  ... | tri> _ _ m<n  = ≼l $ begin
    ω ^ a + ω ^ f m         ≤⟨ a+-pres≼ (a^-pres≼ fm≼fn) ⟩
    ω ^ a + ω ^ f n         ≤⟨ fst (ω^-absorb a≺fn) ⟩
    ω ^ f n                 ∎ where
    fm≼fn =                 begin
      f m                   <⟨ <→≺ (seq-pres m<n) ⟩
      f n                   ∎
```
