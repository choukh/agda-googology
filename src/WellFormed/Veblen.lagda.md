---
title: 形式化大数数学 (2.5 - 超限元Veblen函数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.5 - 超限元Veblen函数)

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

```agda
private variable A : Type
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
instance
  ⟪⟫-nz : {νᵃ : Normal →^ a} → NonZero (⟪ νᵃ ⟫ b 0̇)
  ⟪⟫-nz {(zero)} {b} {νᵃ} = nml-nz νᵃ
  ⟪⟫-nz {suc a} {b} {νᵃ} = nml-nz (νᵃ b 0̇)
  ⟪⟫-nz {lim f} {b} {νᵃ} = nml-nz (νᵃ b 0̇)
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
  jumper = jump Z ⦃ _ ⦄ S +-infl
```

```agda
Φₗ {f} νᵃ zero = νᵃ

Φₗ {f} νᵃ (suc b) = Φ jumper
  module LimSucJump where
  Z : Ord
  Z = lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᵃ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄

  -- might be slightly larger than standard one in some cases, but not a big deal
  S : Ord → ℕ → Func
  S j n x = x + ⟪ Φₗ {f} νᵃ {n} b ⟫ j 0̇

  jumper : Normal
  jumper = jump Z ⦃ _ ⦄ S +-infl

Φₗ {f} νᵃ (lim g) = Φ jumper
  module LimLimJump where
  Z : Ord
  Z = lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᵃ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄

  -- might be slightly larger than standard one in some cases, but not a big deal
  S : Ord → ℕ → Func
  S j n x = x + (⟪ Φₗ {f} νᵃ {n} (g n) ⟫ j 0̇)

  jumper : Normal
  jumper = jump Z ⦃ _ ⦄ S +-infl
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
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₛ νᵃ x 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ νᵃ x 0̇ ⟨ Φₛ νᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ νᵃ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
  Φₛ νᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres₀-rd {νᵃ} {x} (suc {b} r) =      begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres₀-rd r ⟩
  Φₛ νᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (Φₛ νᵃ b 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ νᵃ b 0̇ ⟨ Φₛ νᵃ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ νᵃ b 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
  Φₛ νᵃ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres₀-rd {νᵃ} {x} (lim {f} {n} r) =  begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres₀-rd r ⟩
  Φₛ νᵃ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
  jumper νᵃ f ⟨ 0 ⟩                     ≈˘⟨ Φ-ż ⟩
  Φ (jumper νᵃ f) 0̇ ⟨ 0 ⟩               ∎ where open RoadReasoning; open SucJump
```

```agda
φ : Normal →^ a
φ = Φ ω^
```

```agda
Γ : Normal
Γ = φ {2} 1 0
```

```agda
SVO : Ord
SVO = φ {ω} {0} 1 ⟨ 0 ⟩
```

```agda
ω̇^ : Normal
ω̇^ = normal F F-pres ≈-refl ⦃ ⟪⟫-nz {a = 0} {b = 1} {νᵃ = Φ ω^} ⦄
  module SecondBaseOmega where
  F : Func
  F-pres-rd : F preserves Road
  F-pres : F preserves _<_
  F-pres = map F-pres-rd

  F zero = φ ⟨ 1 ⟩
  F (suc a) = F a + ⟪ φ {suc a} 1 ⟫ 0 0̇
  F (lim f) = lim (F ∘ f) ⦃ F-pres it ⦄

  F-pres-rd zero    = set $ +-infl ⦃ ⟪⟫-nz {b = 0} ⦄
  F-pres-rd (suc r) = rd-trans (F-pres-rd r) (set $ +-infl ⦃ ⟪⟫-nz {b = 0} ⦄)
  F-pres-rd (lim r) = rd-trans (F-pres-rd r) f<l-rd
```

```agda
LVO : Ord
LVO = lfp ω̇^
```
