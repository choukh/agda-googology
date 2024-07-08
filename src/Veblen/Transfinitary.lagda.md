---
title: 形式化大数数学 (1.5 - 超限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.5 - 超限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Transfinitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Transfinitary.lagda.md)  
> 高亮渲染: [Transfinitary.html](https://choukh.github.io/agda-googology/Veblen.Transfinitary.html)  

```agda
{-# OPTIONS --lossy-unification --rewriting --local-confluence-check #-}
module Veblen.Transfinitary where
open import Veblen.Basic public
import Veblen.Finitary as Fin
import Veblen.Infinitary as Inf
```

## 超限元函数类型

```agda
_→^_ : Set → Ord → Set
A →^ zero = A
A →^ suc α = Ord → A →^ α
A →^ lim f = ∀ {n} → Ord → A →^ f n
```

```agda
_0̇ : A →^ α → A
_0̇ {α = zero} = id
_0̇ {α = suc _} F = F 0 0̇
_0̇ {α = lim _} F = F {0} 0 0̇
```

```agda
_0̇,_ : A →^ suc α → A →^ 1
_0̇,_ {α = zero} = id
_0̇,_ {α = suc _} F = F 0 0̇,_
_0̇,_ {α = lim _} F = F 0 {0} 0̇,_
```

## 超限元Veblen函数

```agda
Φₛ : Ord →^ suc α → Ord →^ 2+ α
Φₗ : Ord →^ lim f → Ord →^ suc (lim f)
Φ : Ord →^ 1 → (∀ {α} → Ord →^ suc α)
```

```agda
Φₛ F = rec F
  (λ φ-α → Φ $ fixpt λ β → φ-α β 0̇)
  (λ φ[_] → Φ $ jump λ β → lim λ n → φ[ n ] β 0̇)
```

```agda
Φₗ F = rec F
  (λ φ-α  → Φ $ jump⟨ 1 ⟩ λ β → lim λ n → φ-α {n} β 0̇)
  (λ φ[_] → Φ $ jump (λ β → lim λ m → φ[ m ] {m} β 0̇))
```

```agda
Φ F {α = zero}  = F
Φ F {α = suc α} = Φₛ (Φ F)
Φ F {α = lim f} = Φₗ (Φ F)
```

```agda
φ : ∀ {α} → Ord →^ suc α
φ = Φ (ω ^_)
```

```agda
φ₀ : φ {0} ≡ Fin.φ 0
φ₀ = refl

φ₁ : φ {1} ≡ Fin.φ 1
φ₁ = refl

φ₂ : φ {2} ≡ Fin.φ 2
φ₂ = refl
```

```agda
SVO : Ord
SVO = φ {ω} 1 {0} 0
```

```agda
LVO : Ord
LVO = fixpt (λ α → φ {α} 1 0̇) 0
```

```agda
Φ-ż-α : Φ F {α} 0̇,_ ≡ F
Φ-ż-α {α = zero} = refl
Φ-ż-α {α = suc α} = Φ-ż-α {α = α}
Φ-ż-α {α = lim f} = Φ-ż-α {α = f 0}
{-# REWRITE Φ-ż-α #-}
```

```agda
Φₛ-s-ż-z : (Φ F {suc α} (suc β) 0̇, 0) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) 0
Φₛ-s-ż-z = refl

Φₛ-s-ż-s : (Φ F {suc α} (suc β) 0̇, suc γ) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) (suc (Φ F {suc α} (suc β) 0̇, γ))
Φₛ-s-ż-s = refl

Φₛ-l-ż-z : (Φ F {suc α} (lim g) 0̇, 0) ≡ lim λ n → Φ F {suc α} (g n) 0 0̇
Φₛ-l-ż-z = refl

Φₛ-l-ż-s : (Φ F {suc α} (lim g) 0̇, suc γ) ≡ lim λ n → Φ F {suc α} (g n) (suc (Φ F {suc α} (lim g) 0̇, γ)) 0̇
Φₛ-l-ż-s = refl

Φₛ-β-ż-l : F (lim g) ≡ lim (λ n → F (g n))
  → (Φ F {suc α} β 0̇, lim g) ≡ lim λ n → Φ F {suc α} β 0̇, g n
Φₛ-β-ż-l {β = zero} = id
Φₛ-β-ż-l {β = suc _} _ = refl
Φₛ-β-ż-l {β = lim _} _ = refl
```

```agda
Φₗ-s-ż-z : Φ F {lim f} (suc β) {n} 0̇, 0 ≡ lim λ n → Φ F {lim f} β {n} 1 0̇
Φₗ-s-ż-z = refl

Φₗ-s-ż-s : Φ F {lim f} (suc β) {n} 0̇, suc γ ≡ lim λ n → Φ F {lim f} β {n} (suc (Φ F {lim f} (suc β) {n} 0̇, γ)) 0̇
Φₗ-s-ż-s = refl

Φₗ-l-ż-z : Φ F {lim f} (lim g) {n} 0̇, 0 ≡ lim λ n → Φ F {lim f} (g n) {n} 0 0̇
Φₗ-l-ż-z = refl

Φₗ-l-ż-s : Φ F {lim f} (lim g) {n} 0̇, suc γ ≡ lim λ n → Φ F {lim f} (g n) {n} (suc (Φ F {lim f} (lim g) {n} 0̇, γ)) 0̇
Φₗ-l-ż-s = refl

Φₗ-β-ż-l : F (lim g) ≡ lim (λ n → F (g n))
  → (Φ F {lim f} β {n} 0̇, lim g) ≡ lim λ n → Φ F {lim f} β {n} 0̇, g n
Φₗ-β-ż-l {β = zero} = id
Φₗ-β-ż-l {β = suc _} _ = refl
Φₗ-β-ż-l {β = lim _} _ = refl
```

**例** 一个很大的大数:

```agda
lvo₉₉ : ℕ
lvo₉₉ = FGH.f LVO 99
```
