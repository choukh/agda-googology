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
module FixableJump
  (Z : Ord)
  (⦃ Z-nz ⦄ : NonZero Z)
  (S : Ord → ℕ → Func)
  (S-wf : ∀ {a} → wf (Itₙ (S (suc a)) (suc a)))
  where
  open Jump Z ⦃ Z-nz ⦄ S S-wf renaming (jump to ι)
```

```agda
  F⁺-infl≼ : F⁺ inflates _≼_
  F⁺-infl≼ {(zero)} = z≼
  F⁺-infl≼ {suc x} = ≼[ 0 ] (s≼s F⁺-infl≼)
  F⁺-infl≼ {lim f} = l≼l F⁺-infl≼
```

```agda
  F⁺-isLim : ⦃ NonZero a ⦄ → isLim (F⁺ a)
  F⁺-isLim {suc a} = _
  F⁺-isLim {lim f} = _
```

```agda
  module _
    (Z≼ : ∀ {a} → Z ≼ F⁺ a)
    (S-pres≼ : ∀ {a b c d n} → a ≼ b → c ≼ d → S a n c ≼ S b n d)
    (S-⋟+ : ∀ {a b n} → a + b ≼ S a n b)
    where

    F⁺-pres≼ : F⁺ preserves _≼_
    F⁺-pres≼ z≼ = Z≼
    F⁺-pres≼ (≼l p) = ≼l (F⁺-pres≼ p)
    F⁺-pres≼ (l≼ p) = l≼ (F⁺-pres≼ p)
    F⁺-pres≼ (s≼s {a} {b} p) = l≼l q where
      q : Itₙ (S (suc (F⁺ a))) (suc (F⁺ a)) n ≼ Itₙ (S (suc (F⁺ b))) (suc (F⁺ b)) n
      q {n = zero} = s≼s (F⁺-pres≼ p)
      q {n = suc n} = S-pres≼ (s≼s (F⁺-pres≼ p)) q
```

```agda
    F⁺-absorb-pre : F⁺ a + F⁺ (suc a) [ n ] ≼ F⁺ (suc a) [ suc n ]
    F⁺-absorb-pre {a} {n} =                 begin
      F⁺ a + F⁺ (suc a) [ n ]               ≤⟨ +a-pres≼ ≼-zero ⟩
      suc (F⁺ a) + F⁺ (suc a) [ n ]         ≤⟨ S-⋟+ ⟩
      S (suc (F⁺ a)) n (F⁺ (suc a) [ n ])   ≈⟨ ≈-refl ⟩
      F⁺ (suc a) [ suc n ]                  ∎ where open CrossTreeReasoning
```

```agda
    jump-fixbl : Fixable ι
    jump-fixbl = fixable F⁺-infl≼ F⁺-pres≼ ⦃ F⁺-isLim ⦄ F⁺-absorb-pre

open FixableJump using (jump-fixbl)
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
⟪_⟫ : FNormal →^ a → Ord →^ suc a
⟪_⟫ {(zero)} ν = ν ⟨_⟩
⟪_⟫ {suc a} ν b = ⟪ ν b ⟫
⟪_⟫ {lim f} ν b = ⟪ ν b ⟫
```

```agda
⟪⟫-0 : (νᵃ : FNormal →^ a) → ⟪ νᵃ ⟫ 0 0̇ ≡ νᵃ 0̇ ⟨ 0 ⟩
⟪⟫-0 {(zero)} νᵃ = refl
⟪⟫-0 {suc a} νᵃ = ⟪⟫-0 (νᵃ 0)
⟪⟫-0 {lim f} νᵃ = ⟪⟫-0 (νᵃ 0)
{-# REWRITE ⟪⟫-0 #-}
```

```agda
instance
  ⟪⟫-nz : {νᵃ : FNormal →^ a} → NonZero (⟪ νᵃ ⟫ b 0̇)
  ⟪⟫-nz {(zero)} {b} {νᵃ} = nml-nz (fst νᵃ)
  ⟪⟫-nz {suc a} {b} {νᵃ} = nml-nz (fst $ νᵃ b 0̇)
  ⟪⟫-nz {lim f} {b} {νᵃ} = nml-nz (fst $ νᵃ b 0̇)
```

```agda
private variable
  ν : FNormal
  νᵃ : FNormal →^ a
```

```agda
Φₛ : FNormal →^ a → FNormal →^ suc a
Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → FNormal →^ f n) → FNormal →^ lim f
Φ  : FNormal → (∀ {a} → FNormal →^ a)
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

  jumper : FNormal
  jumper = jump Z ⦃ _ ⦄ S +-infl ,
    jump-fixbl Z S +-infl {!   !} {!   !} {!   !}
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

  jumper : FNormal
  jumper = jump Z ⦃ _ ⦄ S +-infl , {!   !}

Φₗ {f} νᵃ (lim g) = Φ jumper
  module LimLimJump where
  Z : Ord
  Z = lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᵃ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄

  -- might be slightly larger than standard one in some cases, but not a big deal
  S : Ord → ℕ → Func
  S j n x = x + (⟪ Φₗ {f} νᵃ {n} (g n) ⟫ j 0̇)

  jumper : FNormal
  jumper = jump Z ⦃ _ ⦄ S +-infl , {!   !}
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
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (fst $ Φₛ νᵃ x 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ νᵃ x 0̇ ⟨ Φₛ νᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ νᵃ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
  Φₛ νᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres₀-rd {νᵃ} {x} (suc {b} r) =      begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres₀-rd r ⟩
  Φₛ νᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ nml-pres (fst $ Φₛ νᵃ b 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
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
φ : FNormal →^ a
φ = Φ ω^
```

```agda
Γ : FNormal
Γ = φ {2} 1 0
```

```agda
SVO : Ord
SVO = φ {ω} {0} 1 ⟨ 0 ⟩
```

```agda
ω̇^ : FNormal
ω̇^ = normal F F-pres ≈-refl ⦃ ⟪⟫-nz {a = 0} {b = 1} {νᵃ = Φ ω^} ⦄
   , fixable F-infl≼ {!   !} ⦃ {!   !} ⦄ {!   !}
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

  F-infl≼ : F inflates _≼_
  F-infl≼ {(zero)} = z≼
  F-infl≼ {suc x} = ≼-trans (s≼s F-infl≼) (a+-pres≼ $ ≤→≼ $ <→s≤ $ nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄)
  F-infl≼ {lim f} = l≼l F-infl≼

  F-pres≼ : F preserves _≼_
  F-pres≼ {y = zero}  z≼ = ≼-refl
  F-pres≼ {y = suc y} z≼ = ≼-trans (F-pres≼ {y = y} z≼) +a-infl≼
  F-pres≼ {y = lim f} z≼ = ≼l (F-pres≼ {y = f 0} z≼)
  F-pres≼ (s≼s p) = +-pres≼ (F-pres≼ p) {!   !}
  F-pres≼ (≼l p) = {!   !}
  F-pres≼ (l≼ x) = {!   !}
```

```agda
LVO : Ord
LVO = fp ω̇^ ⟨ 0 ⟩
```
