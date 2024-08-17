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
ns→≼ : NSRoad a b → a ≼ b
ns→≼ (inl zero) = ≼-suc ≼-refl
ns→≼ (inl (suc r)) = ≼-suc (ns→≼ (inl r))
ns→≼ (inl (lim r)) = ≼l (ns→≼ (inl r))
ns→≼ (inr refl) = ≼-refl

≤→≼ : a ≤ b → a ≼ b
≤→≼ (inl r) = ns→≼ (inl (set r))
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
l≈ls p = l≼ (λ { {(zero)} → ≼l p
               ; {suc n}  → ≼l ≼-refl })
       , l≼ (≼l ≼-refl)
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
≼→≺s : a ≼ b → a ≺ suc b
≼→≺s z≼ = s≼s z≼
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

≺-≼-trans : Trans _≺_ _≼_ _≺_
≺-≼-trans p q = ≼-trans p q

≼-≺-trans : Trans _≼_ _≺_ _≺_
≼-≺-trans p q = ≼-trans (s≼s p) q

≺-resp-≈ : _≺_ Respects₂ _≈_
≺-resp-≈ = (λ { (p , q) u → ≺-≼-trans u p })
         , (λ { (p , q) u → ≼-≺-trans q u })
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

```agda
private instance
  fin-suc-wf : wf (fin ∘ suc)
  fin-suc-wf = zero₁

  ω^-nz : NonZero (ω ^ a)
  ω^-nz = nz-intro ω^>0
```

```agda
_ : ω + 1 ≡ suc ω
_ = refl
```

```agda
1+ω≈ω : 1 + ω ≈ ω
1+ω≈ω =                       begin-equality
  1 + ω                       ≈⟨ ≈-refl ⟩
  lim- (λ n → 1 + fin n)      ≈⟨ l≈l (≡→≈ +-emb) ⟩
  lim (λ n → fin (suc n))     ≈˘⟨ l≈ls ≼-zero ⟩
  lim- (λ n → fin n)          ≈⟨ ≈-refl ⟩
  ω                           ∎ where open CrossTreeReasoning
```

```agda
+a-infl≼ : (_+ a) inflates _≼_
+a-infl≼ = ≤→≼ +-infl≤
```

```agda
+a-pres≼ : (_+ a) preserves _≼_
+a-pres≼ = {!   !}
```

```agda
a+-pres≼ : (a +_) preserves _≼_
a+-pres≼ z≼ = +a-infl≼
a+-pres≼ (s≼s p) = {!   !}
a+-pres≼ (≼l p) = {!   !}
a+-pres≼ (l≼ x) = {!   !}
```

```agda
ω^-absorb : a ≺ b → ω ^ a + ω ^ b ≈ ω ^ b
ω^-absorb {a} {b = suc b} a≺b =
  (l≼ λ {n} →               begin
    ω ^ a + ω ^ b * fin n   ≤⟨ +a-pres≼ {!   !} ⟩
    ω ^ b + ω ^ b * fin n   ≤⟨ {!   !} ⟩
    ω ^ suc b               ∎)
  ,
  (l≼ λ {n} → {!   !})
  where open CrossTreeReasoning
ω^-absorb {a} {b = lim f} a≺b = {!   !}
```
