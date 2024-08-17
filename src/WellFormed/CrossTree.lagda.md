---
title: 形式化大数数学 (2.2 - 跨树关系)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.2 - 跨树关系)

> 交流Q群: 893531731  
> 本文源码: [CrossTree.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/CrossTree.lagda.md)  
> 高亮渲染: [CrossTree.html](https://choukh.github.io/agda-googology/WellFormed.CrossTree.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.CrossTree where

open import WellFormed.Base
open import WellFormed.Properties
open import Relation.Binary.Definitions
```

## 非严格序

**定义 2-2-x**

```agda
infix 6 _≼_
data _≼_ : Rel where
  z≼  : 0 ≼ a
  s≼s : a ≼ b → suc a ≼ suc b
  ≼l  : {w : wf f} → a ≼ f n → a ≼ lim f ⦃ w ⦄
  l≼  : {w : wf f} → (∀ {n} → f n ≼ a) → lim f ⦃ w ⦄ ≼ a
```

**事实 2-2-x**

```agda
s≼s-inj : suc injects _≼_
s≼s-inj (s≼s p) = p
```

**事实 2-2-x**

```agda
l≼l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≼ g n) → lim f ⦃ wff ⦄ ≼ lim g ⦃ wfg ⦄
l≼l p = l≼ (≼l p)
```

**定理 2-2-x**

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc x} = s≼s ≼-refl
≼-refl {lim f} = l≼ (≼l ≼-refl)
```

**推论 2-2-x**

```agda
f≼l : {w : wf f} → f n ≼ lim f ⦃ w ⦄
f≼l = ≼l ≼-refl
```

**定理 2-2-x**

```agda
≼-trans : Transitive _≼_
≼-trans z≼      q       = z≼
≼-trans (s≼s p) (s≼s q) = s≼s (≼-trans p q)
≼-trans p       (≼l q)  = ≼l (≼-trans p q)
≼-trans (l≼ p)  q       = l≼ (≼-trans p q)
≼-trans (≼l p)  (l≼ q)  = ≼-trans p q
```

**推论 2-2-x**

```agda
l≼-inv : {w : wf f} → lim f ⦃ w ⦄ ≼ a → f n ≼ a
l≼-inv (≼l p) = ≼-trans f≼l (≼l p)
l≼-inv (l≼ p) = p
```

**引理 2-2-x**

```agda
≼-suc : a ≼ b → a ≼ suc b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l p) = ≼-trans (≼-suc p) (s≼s f≼l)
≼-suc (l≼ p) = l≼ (≼-suc p)

≼-zero : a ≼ suc a
≼-zero = ≼-suc ≼-refl
```

**定理 2-2-x**

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

**定义 2-2-x**

```agda
_≈_ : Rel
a ≈ b = a ≼ b × b ≼ a
```

**事实 2-2-x**

```agda
≼-antisym : Antisymmetric _≈_ _≼_
≼-antisym p q = p , q
```

**定理 2-2-x**

```agda
≈-refl : Reflexive _≈_
≈-refl = ≼-refl , ≼-refl

≈-sym : Symmetric _≈_
≈-sym (p , q) = q , p

≈-trans : Transitive _≈_
≈-trans (p , q) (u , v) = ≼-trans p u , ≼-trans v q
```

**事实 2-2-x**

```agda
s≈s : a ≈ b → suc a ≈ suc b
s≈s (p , q) = s≼s p , s≼s q

s≈s-inj : suc injects _≈_
s≈s-inj (p , q) = s≼s-inj p , s≼s-inj q
```

**事实 2-2-x**

```agda
l≈l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≈ g n) → lim f ⦃ wff ⦄ ≈ lim g ⦃ wfg ⦄
l≈l p = l≼l (fst p) , l≼l (snd p)
```

**事实 2-2-x**

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
s⋠ : suc a ⋠ a
l⋠f : {w : wf f} → lim f ⦃ w ⦄ ⋠ f n
l⋠f p = s⋠ (≼-trans (≤→≼ (<→s≤ f<l)) p)

s⋠ {suc a} p = s⋠ (s≼s-inj p)
s⋠ {lim f} (≼l p) = l⋠f (≼-trans ≼-zero p)
```

```agda
≺-irrefl : Irreflexive _≈_ _≺_
≺-irrefl (_ , p) q = s⋠ (≼-trans q p)
```
