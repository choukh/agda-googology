---
title: 形式化大数数学 (2.5 - Veblen层级)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.5 - Veblen层级)

> 交流Q群: 893531731  
> 本文源码: [Veblen.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Veblen.lagda.md)  
> 高亮渲染: [Veblen.html](https://choukh.github.io/agda-googology/WellFormed.Veblen.html)  

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module WellFormed.Veblen where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
open import WellFormed.CrossTree
open import WellFormed.Fixpoints

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
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
    Z : Ord
    Z = lim (λ n → Φ (f n) ⟨ 0 ⟩) ⦃ Φ-pres₀ it ⦄

    -- slightly larger than standard one, but not a big deal
    S : Ord → ℕ → Func
    S j n x = x + Φ (f n) ⟨ j ⟩

    jumper : Normal
    jumper = jump Z S (+-infl ⦃ Φ-nz ⦄)
```

```agda
  Φ-nz {(zero)} = nml-nz ν
  Φ-nz {suc a}  = nml-nz (Φ (suc a))
  Φ-nz {lim f}  = nml-nz (Φ (lim f))
```

```agda
  Φ-pres₀-rd zero        = rd[ 2 ] $ set $ nml-pres (Φ _) nz-elim
  Φ-pres₀-rd (suc r)     = rd[ 1 ] $ Φ-pres₀-rd r
  Φ-pres₀-rd (lim {n} r) = rd[ n ] $ Φ-pres₀-rd r
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
  Γ : Normal
  Γ = fp (normal (λ a → φ a ⟨ 0 ⟩) (Φ-pres₀ ω^) refl)
```

## 有限元Veblen函数

```agda
module Finitary where
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
  ⟪⟫-0 : {νⁿ : Normal →ⁿ n} → ⟪ νⁿ ⟫ 0̇ ≡ νⁿ 0̇ ⟨ 0 ⟩
  ⟪⟫-0 {(zero)} = refl
  ⟪⟫-0 {suc n} = ⟪⟫-0 {n}
  --{-# REWRITE ⟪⟫-0 #-}
```

```agda
  ⟪⟫-nz : (νⁿ : Normal →ⁿ n) → NonZero (⟪ νⁿ ⟫ a 0̇)
  ⟪⟫-nz {(zero)} νⁿ = nml-nz νⁿ
  ⟪⟫-nz {suc n} {a} νⁿ = ⟪⟫-nz {n} (νⁿ a)
```

```agda
  private variable
    ν : Normal
    νⁿ : Normal →ⁿ n
```

```agda
  Φₙ : Normal →ⁿ n → Normal →ⁿ suc n
  Φ  : Normal → (∀ {n} → Normal →ⁿ n)
```

```agda
  Φₙ-nz : NonZero (⟪ Φₙ νⁿ a ⟫ b 0̇)
  Φₙ-nz = ⟪⟫-nz (Φₙ _ _)

  Φ-nz : NonZero (⟪ Φ ν {n} ⟫ a 0̇)
  Φ-nz {ν} = Φₙ-nz {νⁿ = Φ ν} {a = 0}
```

```agda
  Φₙ-pres₀-rd : (λ x → ⟪ Φₙ {n} νⁿ x ⟫ 0̇) preserves Road
  Φₙ-pres₀ : (λ x → ⟪ Φₙ {n} νⁿ x ⟫ 0̇) preserves _<_
  Φₙ-pres₀ = map Φₙ-pres₀-rd

  Φ-pres₀ : (λ x → ⟪ Φ ν {suc n} x ⟫ 0̇) preserves _<_
  Φ-pres₀ = Φₙ-pres₀
```

```agda
  Φₙ {n} νⁿ zero = νⁿ
  Φₙ {n} νⁿ (suc a) = Φ (fp (Φₙ νⁿ a 0̇))
  Φₙ {n} νⁿ (lim f) = Φ jumper
    module FinitaryJump where
    Z : Ord
    Z = lim (λ n → ⟪ Φₙ νⁿ (f n) ⟫ 0̇) ⦃ Φₙ-pres₀ it ⦄

    -- slightly larger than standard one, but not a big deal
    S : Ord → ℕ → Func
    S j n x = x + ⟪ Φₙ νⁿ (f n) ⟫ j 0̇

    jumper : Normal
    jumper = jump Z ⦃ _ ⦄ S (+-infl ⦃ Φₙ-nz ⦄)
```

```agda
  Φ ν {n = zero}  = ν
  Φ ν {n = suc n} = Φₙ (Φ ν)
```

```agda
  Φₙ-pres₀-rd {(zero)} zero = rd[ 2 ] $ set $ nml-pres (Φₙ _ _) (nz-elim ⦃ Φₙ-nz {0} ⦄)
  Φₙ-pres₀-rd {suc zero} zero = {!   !} --rd[ 2 ] $ set $ nml-pres (Φₙ _ _ _) (nz-elim ⦃ Φₙ-nz {1} ⦄)
  Φₙ-pres₀-rd {2+ zero} {(νⁿ)} {(x)} zero = {! fp (Φₙ νⁿ x 0 0) ⟨ 0 ⟩ !}
  Φₙ-pres₀-rd {2+ (suc n)} {(νⁿ)} {(x)} zero = subst (Road _) (sym ⟪⟫-0) {!   !}
  Φₙ-pres₀-rd (suc r) = {! Φₙ νⁿ (suc x)  !}
  Φₙ-pres₀-rd (lim r) = {!   !}
```

```agda
  φ : ∀ {n} → Normal →ⁿ n
  φ = Φ ω^
```

```agda
  instance _ = Φ-nz
  SVO : Ord
  SVO = lim (Itₙ (λ n x → x + ⟪ φ {n} ⟫ 1 0̇) 0) ⦃ +-infl ⦄
```
