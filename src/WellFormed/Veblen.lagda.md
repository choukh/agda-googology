---
title: 形式化大数数学 (2.5 - Veblen层级)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.5 - Veblen层级)

> 交流Q群: 893531731  
> 本文源码: [Veblen.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Veblen.lagda.md)  
> 高亮渲染: [Veblen.html](https://choukh.github.io/agda-googology/WellFormed.Veblen.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Veblen where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
open import WellFormed.CrossTree
open import WellFormed.Fixpoints
```

## 二元Veblen函数

```agda
module BinaryAux (ν : Normal) where

  Φ : Ord → Normal
  Φ-nz : NonZero (Φ a ⟨ b ⟩)
  instance _ = Φ-nz

  Φ-pres₀-rd : (λ x → Φ x ⟨ 0 ⟩) preserves Road
  Φ-pres₀ : (λ x → Φ x ⟨ 0 ⟩) preserves _<_
  Φ-pres₀ = map Φ-pres₀-rd
```

```agda
  Φ zero = ν
  Φ (suc a) = fp (Φ a)
  Φ (lim f) = jumper
    module BinaryVeblenJump where
    instance _ = Φ-nz

    Z : Ord
    Z = lim (λ n → Φ (f n) ⟨ 0 ⟩) ⦃ Φ-pres₀ it ⦄

    S : Ord → ℕ → Func
    S j n x = x + Φ (f n) ⟨ j ⟩

    jumper : Normal
    jumper = jump Z S +-infl
```

```agda
  Φ-nz {(zero)} = nml-nz ν
  Φ-nz {suc a}  = nml-nz (Φ (suc a))
  Φ-nz {lim f}  = nml-nz (Φ (lim f))
```

```agda
  Φ-pres₀-rd zero        = rd[ 2 ] (set (nml-pres (Φ _) nz-elim))
  Φ-pres₀-rd (suc r)     = rd[ 1 ] (Φ-pres₀-rd r)
  Φ-pres₀-rd (lim {n} r) = rd[ n ] (Φ-pres₀-rd r)
```

```agda
module Binary where
  open BinaryAux

  φ : Ord → Normal
  φ = Φ ω^
```

```agda
  φ-0 : φ 0 ≡ ω^
  φ-0 = refl

  φ-suc : φ (suc a) ≡ fp (φ a)
  φ-suc = refl

  φ-lim-0 : ⦃ _ : wf f ⦄ → φ (lim f) ⟨ 0 ⟩ ≡ lim- λ n → φ (f n) ⟨ 0 ⟩
  φ-lim-0 = refl

  φ-lim-suc : ⦃ _ : wf f ⦄ → φ (lim f) ⟨ suc a ⟩ ≡ lim- λ n → Itₙ (λ n x → x + φ (f n) ⟨ suc (φ (lim f) ⟨ a ⟩) ⟩) (suc (φ (lim f) ⟨ a ⟩)) n
  φ-lim-suc = refl

  φ-lim-lim : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → φ (lim f) ⟨ lim g ⟩ ≡ lim- λ n → φ (lim f) ⟨ g n ⟩
  φ-lim-lim = refl
```

```agda
  Γ₀ : Normal
  Γ₀ = fp (normal (λ a → φ a ⟨ 0 ⟩) (Φ-pres₀ ω^) refl)
```

## 有限元Veblen函数

```agda
module FinitaryAux where
  private variable A : Type
```

```agda
  _→ⁿ_ : Set → ℕ → Set
  A →ⁿ zero = A
  A →ⁿ suc n = Ord → A →ⁿ n
```

```agda
  _0̇ : A →ⁿ n → A
  _0̇ {n = zero} = id
  _0̇ {n = suc n} F = F 0 0̇
```

```agda
  _0̇,_ : A →ⁿ suc n → A →ⁿ 1
  _0̇,_ {n = zero} = id
  _0̇,_ {n = suc n} F = F 0 0̇,_
```

```agda
  ⟪_⟫ : Normal →ⁿ n → Ord →ⁿ suc n
  ⟪_⟫ {(zero)} ν = ν ⟨_⟩
  ⟪_⟫ {suc n} ν a = ⟪ ν a ⟫
```

```agda
  Φₙ : Normal →ⁿ n → Normal →ⁿ suc n
  Φ  : Normal → (∀ {n} → Normal →ⁿ n)

  Φₙ-nz : {νⁿ : Normal →ⁿ n} → NonZero (⟪ Φₙ νⁿ a ⟫ (suc b) 0̇)
```

```agda
  Φₙ {n} νⁿ zero = νⁿ
  Φₙ {n} νⁿ (suc a) = Φ (fp (Φₙ νⁿ a 0̇))
  Φₙ {n} νⁿ (lim f) = Φ jumper
    module FinitaryJump where
    instance _ = Φₙ-nz

    Z : Ord
    Z = lim (λ m → ⟪ Φₙ νⁿ (f n) ⟫ 0̇) ⦃ {!   !} ⦄

    S : Ord → ℕ → Func
    S j n x = x + ⟪ Φₙ νⁿ (f n) ⟫ j 0̇

    jumper : Normal
    jumper = jump Z S +-infl
```

```agda
  Φ ν {n = zero}  = ν
  Φ ν {n = suc n} = Φₙ (Φ ν)
```

```agda
  Φₙ-nz {n} {a = zero} = {!   !}
  Φₙ-nz {n} {a = suc a} = {!   !}
  Φₙ-nz {n} {a = lim f} = {!   !}
```
