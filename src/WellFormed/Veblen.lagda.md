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

    -- slightly larger than standard one in some cases, but not a big deal
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
  ⟪⟫-0 : (νⁿ : Normal →ⁿ n) → ⟪ νⁿ ⟫ 0 0̇ ≡ νⁿ 0̇ ⟨ 0 ⟩
  ⟪⟫-0 {(zero)} νⁿ = refl
  ⟪⟫-0 {suc n} νⁿ = ⟪⟫-0 (νⁿ 0)
  {-# REWRITE ⟪⟫-0 #-}
```

```agda
  ⟪⟫-nz : (νⁿ : Normal →ⁿ n) → NonZero (⟪ νⁿ ⟫ a 0̇)
  ⟪⟫-nz {(zero)} νⁿ = nml-nz νⁿ
  ⟪⟫-nz {suc n} {a} νⁿ = nml-nz (νⁿ a 0̇)
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
```

```agda
  Φₙ-pres₀-rd : (λ x → Φₙ {n} νⁿ x 0̇ ⟨ 0 ⟩) preserves Road
  Φₙ-pres₀ : (λ x → Φₙ {n} νⁿ x 0̇ ⟨ 0 ⟩) preserves _<_
  Φₙ-pres₀ = map Φₙ-pres₀-rd
```

```agda
  Φₙ νⁿ zero = νⁿ
  Φₙ νⁿ (suc a) = Φ (fp (Φₙ νⁿ a 0̇))
  Φₙ νⁿ (lim f) = Φ jumper
    module FinitaryJump where
    Z : Ord
    Z = lim (λ n → Φₙ νⁿ (f n) 0̇ ⟨ 0 ⟩) ⦃ Φₙ-pres₀ it ⦄

    -- slightly larger than standard one in some cases, but not a big deal
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
  Φ-ż : Φ ν {n} 0̇ ⟨ 0 ⟩ ≡ ν ⟨ 0 ⟩
  Φ-ż {n = zero} = refl
  Φ-ż {n = suc n} = Φ-ż {n = n}
```

```agda
  Φₙ-pres₀-rd {νⁿ} {x} zero =             begin-strict
    Φₙ νⁿ x 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₙ νⁿ x 0̇) (nz-elim ⦃ Φₙ-nz {b = 0} ⦄) ⟩
    Φₙ νⁿ x 0̇ ⟨ Φₙ νⁿ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
    fp (Φₙ νⁿ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
    Φₙ νⁿ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
  Φₙ-pres₀-rd {νⁿ} {x} (suc {b} r) =      begin-strict
    Φₙ νⁿ x 0̇ ⟨ 0 ⟩                       <⟨ Φₙ-pres₀-rd r ⟩
    Φₙ νⁿ b 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₙ νⁿ b 0̇) (nz-elim ⦃ Φₙ-nz {b = 0} ⦄) ⟩
    Φₙ νⁿ b 0̇ ⟨ Φₙ νⁿ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
    fp (Φₙ νⁿ b 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
    Φₙ νⁿ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
  Φₙ-pres₀-rd {νⁿ} {x} (lim {f} {n} r) =  begin-strict
    Φₙ νⁿ x 0̇ ⟨ 0 ⟩                       <⟨ Φₙ-pres₀-rd r ⟩
    Φₙ νⁿ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
    jumper νⁿ f ⟨ 0 ⟩                     ≈˘⟨ Φ-ż ⟩
    Φ (jumper νⁿ f) 0̇ ⟨ 0 ⟩               ∎ where open RoadReasoning; open FinitaryJump
```

```agda
  φ : ∀ {n} → Normal →ⁿ n
  φ = Φ ω^
```

```agda
  φ-nz : NonZero (⟪ φ {n} ⟫ a 0̇)
  φ-nz = Φₙ-nz {νⁿ = φ} {a = 0}
```

```agda
  SVO : Ord
  SVO = lim (Itₙ (λ n x → x + ⟪ φ {n} ⟫ 1 0̇) 0) ⦃ +-infl ⦃ φ-nz ⦄ ⦄
```

## 超限元Veblen函数

```agda
module Transfinitary where
  private variable A : Type
```

```agda
  _→^_ : Type → Ord → Type
  A →^ zero = A
  A →^ suc a = Ord → A →^ a
  A →^ lim f = ∀ {n} → Ord → A →^ f n
```

```agda
  _0̇ : A →^ a → A
  _0̇ {a = zero} = id
  _0̇ {a = suc a} F = F 0 0̇
  _0̇ {a = lim f} F = F {0} 0 0̇
```

```agda
  _0̇,_ : A →^ suc a → A →^ 1
  _0̇,_ {a = zero} = id
  _0̇,_ {a = suc a} F = F 0 0̇,_
  _0̇,_ {a = lim f} F = F 0 {0} 0̇,_
```

```agda
  ⟪_⟫ : Normal →^ a → Ord →^ suc a
  ⟪_⟫ {(zero)} ν = ν ⟨_⟩
  ⟪_⟫ {suc a} ν b = ⟪ ν b ⟫
  ⟪_⟫ {lim f} ν b = ⟪ ν b ⟫
```

```agda
  ⟪⟫-0 : (νᵃ : Normal →^ a) → ⟪ νᵃ ⟫ 0 0̇ ≡ νᵃ 0̇ ⟨ 0 ⟩
  ⟪⟫-0 {(zero)} νᵃ = refl
  ⟪⟫-0 {suc a} νᵃ = ⟪⟫-0 (νᵃ 0)
  ⟪⟫-0 {lim f} νᵃ = ⟪⟫-0 (νᵃ 0)
  {-# REWRITE ⟪⟫-0 #-}
```

```agda
  ⟪⟫-nz : (νᵃ : Normal →^ a) → NonZero (⟪ νᵃ ⟫ b 0̇)
  ⟪⟫-nz {(zero)} νⁿ = nml-nz νⁿ
  ⟪⟫-nz {suc a} {b} νⁿ = nml-nz (νⁿ b 0̇)
  ⟪⟫-nz {lim f} {b} νⁿ = nml-nz (νⁿ b 0̇)
```

```agda
  private variable
    ν : Normal
    νᵃ : Normal →^ a
```

```agda
  Φₛ : Normal →^ a → Normal →^ suc a
  Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → Normal →^ f n) → Normal →^ lim f
  Φ  : Normal → (∀ {a} → Normal →^ a)
```

```agda
  Φₛ-nz : NonZero (⟪ Φₛ νᵃ b ⟫ c 0̇)
  Φₛ-nz = ⟪⟫-nz (Φₛ _ _)
```

```agda
  Φₗ-nz : ⦃ _ : wf f ⦄ {νᵃ : ∀ {n} → Normal →^ f n} → NonZero (⟪ Φₗ {f} νᵃ {n} b ⟫ c 0̇)
  Φₗ-nz = ⟪⟫-nz (Φₗ _ _)
```

```agda
  Φₛ-pres₀-rd : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) preserves Road
  Φₛ-pres₀ : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) preserves _<_
  Φₛ-pres₀ = map Φₛ-pres₀-rd
```

```agda
  Φₛ {a} νᵃ zero = νᵃ
  Φₛ {a} νᵃ (suc b) = Φ (fp (Φₛ νᵃ b 0̇))
  Φₛ {a} νᵃ (lim g) = Φ jumper
    module SucJump where
    Z : Ord
    Z = lim (λ n → Φₛ νᵃ (g n) 0̇ ⟨ 0 ⟩) ⦃ Φₛ-pres₀ it ⦄

    -- might be slightly larger than standard one in some cases, but not a big deal
    S : Ord → ℕ → Func
    S j n x = x + ⟪ Φₛ νᵃ (g n) ⟫ j 0̇

    jumper : Normal
    jumper = jump Z ⦃ _ ⦄ S (+-infl ⦃ Φₛ-nz ⦄)
```

```agda
  Φₗ {f} νᵃ zero = νᵃ

  Φₗ {f} νᵃ (suc b) = Φ jumper
    module LimSucJump where
    Z : Ord
    Z = lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᵃ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ Φₗ-nz ⦄ ⦄

    -- might be slightly larger than standard one in some cases, but not a big deal
    S : Ord → ℕ → Func
    S j n x = x + (⟪ Φₗ {f} νᵃ {n} b ⟫ j 0̇)

    jumper : Normal
    jumper = jump Z ⦃ _ ⦄ S (+-infl ⦃ Φₗ-nz ⦄)

  Φₗ {f} νᵃ (lim g) = Φ jumper
    module LimLimJump where
    Z : Ord
    Z = lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᵃ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ Φₗ-nz ⦄ ⦄

    -- might be slightly larger than standard one in some cases, but not a big deal
    S : Ord → ℕ → Func
    S j n x = x + (⟪ Φₗ {f} νᵃ {n} (g n) ⟫ j 0̇)

    jumper : Normal
    jumper = jump Z ⦃ _ ⦄ S (+-infl ⦃ Φₗ-nz ⦄)
```

```agda
  Φ ν {(zero)} = ν
  Φ ν {suc a} = Φₛ {a} (Φ ν)
  Φ ν {lim f} = Φₗ {f} (Φ ν)
```

```agda
  Φ-ż : Φ ν {a} 0̇ ⟨ 0 ⟩ ≡ ν ⟨ 0 ⟩
  Φ-ż {a = zero} = refl
  Φ-ż {a = suc a} = Φ-ż {a = a}
  Φ-ż {a = lim f} = Φ-ż {a = f 0}
```

```agda
  Φₛ-pres₀-rd {νᵃ} {x} zero =             begin-strict
    Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₛ νᵃ x 0̇) (nz-elim ⦃ Φₛ-nz {c = 0} ⦄) ⟩
    Φₛ νᵃ x 0̇ ⟨ Φₛ νᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
    fp (Φₛ νᵃ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
    Φₛ νᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
  Φₛ-pres₀-rd {νᵃ} {x} (suc {b} r) =      begin-strict
    Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres₀-rd r ⟩
    Φₛ νᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₛ νᵃ b 0̇) (nz-elim ⦃ Φₛ-nz {c = 0} ⦄) ⟩
    Φₛ νᵃ b 0̇ ⟨ Φₛ νᵃ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
    fp (Φₛ νᵃ b 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
    Φₛ νᵃ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
  Φₛ-pres₀-rd {νᵃ} {x} (lim {f} {n} r) =  begin-strict
    Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres₀-rd r ⟩
    Φₛ νᵃ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
    jumper νᵃ f ⟨ 0 ⟩                     ≈˘⟨ Φ-ż ⟩
    Φ (jumper νᵃ f) 0̇ ⟨ 0 ⟩               ∎ where open RoadReasoning; open SucJump
```
