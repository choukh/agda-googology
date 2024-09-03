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
{-# REWRITE +a-id #-}
```

## 强正规跳出

```agda
record Jump : Type where
  constructor by
  field
    init : Ord
    step : ℕ → Func
    ⦃ init-nz ⦄ : NonZero init
    ⦃ step-nz ⦄ : NonZero (step n b)
    step-infl≼ : (step n) inflates _≼_
    step-pres≼ : (step n) preserves _≼_
    step-pres-n : step n a ≼ step (suc n) a
```

```agda
  F⁺ : Func
  F⁺-pres-rd : F⁺ preserves Road
  F⁺-pres : F⁺ preserves _<_
  F⁺-pres = map F⁺-pres-rd
```

```agda
  It : Ord → Seq
  It a = Itₙ (λ n x → x + step n (suc (F⁺ a))) 0
```

```agda
  F⁺ zero    = init
  -- might be slightly larger than standard one in some cases, but not a big deal
  F⁺ (suc a) = suc (F⁺ a) + lim (It a) ⦃ +-infl ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄
```

```agda
  F⁺-pres-rd zero         = rd[ 0 ] $ zero
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ suc $ F⁺-pres-rd r
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r
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
  F⁺-pres≼ : F⁺ preserves _≼_
  F⁺-pres≼ {y = zero} z≼ = ≼-refl
  F⁺-pres≼ {y = suc y} z≼ = ≼[ 0 ] (≼-suc (F⁺-pres≼ z≼))
  F⁺-pres≼ {y = lim f} z≼ = ≼[ 0 ] (F⁺-pres≼ z≼)
  F⁺-pres≼ (≼l p) = ≼l (F⁺-pres≼ p)
  F⁺-pres≼ (l≼ p) = l≼ (F⁺-pres≼ p)
  F⁺-pres≼ (s≼s {a} {b} p) = l≼l (+-pres≼ (s≼s (F⁺-pres≼ p)) q) where
    q : It a n ≼ It b n
    q {(zero)} = ≼-refl
    q {suc n} = +-pres≼ q $ step-pres≼ $ s≼s $ F⁺-pres≼ p
```

```agda
  F⁺[n]≼ : F⁺ (suc a) [ n ] ≼ It a (suc n)
  F⁺[n]≼ {a} {(zero)} = step-infl≼
  F⁺[n]≼ {a} {suc n} =                    begin
    F⁺ (suc a) [ suc n ]                  ≈⟨ ≈-refl ⟩
    suc (F⁺ a) + (It a n + step n _)      ≈⟨ ≡→≈ +-assoc ⟩
    (suc (F⁺ a) + It a n) + step n _      ≤⟨ +-pres≼ F⁺[n]≼ step-pres-n ⟩
    (It a n + step n _) + step (suc n) _  ≈⟨ ≈-refl ⟩
    It a (2+ n)                           ∎ where open CrossTreeReasoning
```

```agda
  F⁺-absorb-n : F⁺ a + F⁺ (suc a) [ n ] ≼ F⁺ (suc a) [ suc n ]
  F⁺-absorb-n = +-pres≼ ≼-zero F⁺[n]≼
```

```agda
  jump_ : SNormal
  jump_ = normal F⁺ F⁺-pres ≈-refl , strong F⁺-infl≼ F⁺-pres≼ ⦃ F⁺-isLim ⦄ F⁺-absorb-n
open Jump
```

```agda
module _ {j k : Jump}
  (init≼ : init j ≼ init k)
  (step≼ : ∀ {n a b} → a ≼ b → step j n a ≼ step k n b) where

  It-pres≼ : It j a n ≼ It k a n
  jump-pres≼ : F⁺ j a ≼ F⁺ k a

  It-pres≼ {n = zero} = ≼-refl
  It-pres≼ {n = suc n} = +-pres≼ It-pres≼ (step≼ (s≼s jump-pres≼))

  jump-pres≼ {(zero)} = init≼
  jump-pres≼ {suc a} = l≼l (+-pres≼ (s≼s jump-pres≼) It-pres≼)
  jump-pres≼ {lim f} = l≼l jump-pres≼
```

## 序元函数

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
⟪_⟫ : SNormal →^ a → Ord →^ suc a
⟪_⟫ {(zero)} ν = ν ⟨_⟩
⟪_⟫ {suc a} ν b = ⟪ ν b ⟫
⟪_⟫ {lim f} ν b = ⟪ ν b ⟫
```

```agda
⟪⟫-0 : (νᵃ : SNormal →^ a) → ⟪ νᵃ ⟫ 0 0̇ ≡ νᵃ 0̇ ⟨ 0 ⟩
⟪⟫-0 {(zero)} νᵃ = refl
⟪⟫-0 {suc a} νᵃ = ⟪⟫-0 (νᵃ 0)
⟪⟫-0 {lim f} νᵃ = ⟪⟫-0 (νᵃ 0)
{-# REWRITE ⟪⟫-0 #-}
```

```agda
instance
  ⟪⟫-nz : {νᵃ : SNormal →^ a} → NonZero (⟪ νᵃ ⟫ b 0̇)
  ⟪⟫-nz {(zero)} {b} {νᵃ} = Normal.nz (fst νᵃ)
  ⟪⟫-nz {suc a} {b} {νᵃ} = Normal.nz (fst $ νᵃ b 0̇)
  ⟪⟫-nz {lim f} {b} {νᵃ} = Normal.nz (fst $ νᵃ b 0̇)
```

```agda
private variable
  x y : Ord
  ν ν₁ ν₂ : SNormal
  νᵃ : SNormal →^ a
```

```agda
Φ : SNormal → SNormal →^ a
```

```agda
HSNormal : Ord → SNormal → Type
HSNormal a ν = Σ (SNormal →^ a) (λ Φᵃ → Φᵃ ≡ Φ ν)
private variable Φ̇ᵃ : HSNormal a ν
```

```agda
Φₛ : HSNormal a ν → SNormal →^ suc a
Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → HSNormal (f n) ν) → SNormal →^ lim f
```

```agda
Φₛ-pres-rd : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) preserves Road
Φₛ-pres : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) preserves _<_
Φₛ-pres = map Φₛ-pres-rd
```

```agda
Φ-infl≼-x0   : (λ x → ⟪ Φ {a} ν ⟫ x 0̇) inflates _≼_
Φₛ-infl≼-x0  : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) inflates _≼_
Φₛ-infl≼-bx0 : (λ x → ⟪ Φₛ {a} Φ̇ᵃ b ⟫ x 0̇) inflates _≼_
Φₗ-infl≼-x0  : ⦃ _ : wf f ⦄ {Φ̇ᶠ : ∀ {n} → HSNormal (f n) ν} →
                (λ x → Φₗ {f} Φ̇ᶠ {n} x 0̇ ⟨ 0 ⟩) inflates _≼_
```

```agda
Φ {(zero)} ν = ν
Φ {suc a} ν = Φₛ {a} (Φ ν , refl)
Φ {lim f} ν = Φₗ {f} (Φ ν , refl)
```

```agda
Φₛ Φ̇ᵃ zero = fst Φ̇ᵃ
Φₛ Φ̇ᵃ (suc b) = Φ (fp (Φₛ Φ̇ᵃ b 0̇))
Φₛ Φ̇ᵃ (lim g) = Φ $ jump by
  (lim (λ n → Φₛ Φ̇ᵃ (g n) 0̇ ⟨ 0 ⟩) ⦃ Φₛ-pres it ⦄)
  (λ n x → ⟪ Φₛ Φ̇ᵃ (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ Φₛ-infl≼-bx0 {!   !} {!   !}
```

```agda
Φₗ {f} Φ̇ᶠ zero = fst Φ̇ᶠ
Φₗ {f} Φ̇ᶠ (suc b) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} Φ̇ᶠ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} Φ̇ᶠ {n} b ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!    !} {!   !} {!   !}
Φₗ {f} Φ̇ᶠ (lim g) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} Φ̇ᶠ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} Φ̇ᶠ {n} (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!   !} {!   !} {!   !}
```

```agda
Φ-0b : ν ⟨ b ⟩ ≡ Φ {a} ν 0̇ ⟨ b ⟩
Φ-0b {a = zero} = refl
Φ-0b {a = suc a} = Φ-0b {a = a}
Φ-0b {a = lim f} = Φ-0b {a = f 0}
```

```agda
Φₛ-pres-rd {Φ̇ᵃ} {x} zero =              begin-strict
  Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ Φ̇ᵃ x 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ Φ̇ᵃ x 0̇ ⟨ Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ Φ̇ᵃ x 0̇) ⟨ 0 ⟩                  ≈⟨ Φ-0b ⟩
  Φₛ Φ̇ᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {Φ̇ᵃ} {x} (suc {b} r) =       begin-strict
  Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ Φ̇ᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ Φ̇ᵃ b 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ Φ̇ᵃ b 0̇ ⟨ Φₛ Φ̇ᵃ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ Φ̇ᵃ b 0̇) ⟨ 0 ⟩                  ≈⟨ Φ-0b ⟩
  Φₛ Φ̇ᵃ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {Φ̇ᵃ} {x} (lim {f} {n} r) =   begin-strict
  Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ Φ̇ᵃ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
  (jump _) ⟨ 0 ⟩                        ≈⟨ Φ-0b ⟩
  Φ (jump _) 0̇ ⟨ 0 ⟩                    ∎ where open RoadReasoning
```

```agda
Φ-infl≼-x0 {(zero)} {ν} = Strong.infl≼ (srg ν)
Φ-infl≼-x0 {suc a} = Φₛ-infl≼-x0
Φ-infl≼-x0 {lim f} = Φₗ-infl≼-x0
```

```agda
Φₛ-Φₛ-infl≺ : x ≺ Φₛ Φ̇ᵃ x 0̇ ⟨ Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩ ⟩
Φₛ-Φₛ-infl≺ {x} {Φ̇ᵃ} =                  begin
  suc x                                 ≤⟨ s≼s Φₛ-infl≼-x0 ⟩
  suc (Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩)                 ≤⟨ <→≺ (pres (nz-elim ⦃ zero-nz ⦄)) ⟩
  Φₛ Φ̇ᵃ x 0̇ ⟨ Φₛ Φ̇ᵃ x 0̇ ⟨ 0 ⟩ ⟩         ∎ where open CrossTreeReasoning; open Normal (nml $ Φₛ Φ̇ᵃ x 0̇)
```

```agda
Φₛ-infl≼-x0 {Φ̇ᵃ} {(zero)} = z≼
Φₛ-infl≼-x0 {Φ̇ᵃ} {suc x} = subst (suc x ≼_) Φ-0b $ ≼[ 2 ] Φₛ-Φₛ-infl≺
Φₛ-infl≼-x0 {Φ̇ᵃ} {lim f} = subst (lim f ≼_) Φ-0b $ l≼l Φₛ-infl≼-x0
```

```agda
Φₗ-infl≼-x0 {Φ̇ᶠ} {(zero)} = z≼
Φₗ-infl≼-x0 {Φ̇ᶠ} {suc x} = subst (suc x ≼_) Φ-0b $ ≼[ 1 ] $ {!   !}
Φₗ-infl≼-x0 {Φ̇ᶠ} {lim f} = subst (lim f ≼_) Φ-0b $ l≼ls $ ≼-trans Φₗ-infl≼-x0 a+-infl≼
```

```agda
Φₛ-infl≼-bx0 {(zero)}  {Φ̇ᵃ = Φᵃ , refl} {(zero)} = Strong.infl≼ (srg Φᵃ)
Φₛ-infl≼-bx0 {lim f}   {Φ̇ᵃ = Φᵃ , refl} {(zero)} = Φ-infl≼-x0
Φₛ-infl≼-bx0 {suc a}   {Φ̇ᵃ = Φᵃ , refl} {(zero)} = Φ-infl≼-x0
Φₛ-infl≼-bx0 {(zero)}  {Φ̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {suc a}   {Φ̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {lim f}   {Φ̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {(zero)}  {Φ̇ᵃ} {lim f}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {suc a}   {Φ̇ᵃ} {lim g}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {lim f}   {Φ̇ᵃ} {lim g}  = Φ-infl≼-x0
```
