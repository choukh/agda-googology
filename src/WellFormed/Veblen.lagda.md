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
record Jumper : Type where
  constructor jumper
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
  jump : SNormal
  jump = normal F⁺ F⁺-pres ≈-refl , strong F⁺-infl≼ F⁺-pres≼ ⦃ F⁺-isLim ⦄ F⁺-absorb-n
open Jumper
```

```agda
module _ {j k : Jumper}
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

## 主互递归声明

```agda
Φ : SNormal → SNormal →^ a
```

```agda
ΦSegment : Ord → SNormal → Type
ΦSegment a ν = Σ (SNormal →^ a) (λ Φᵃ → Φᵃ ≡ Φ ν)
private variable Φ̇ᵃ Φ̇ᵃ₁ Φ̇ᵃ₂ : ΦSegment a ν
```

```agda
Φₛ : ΦSegment a ν → SNormal →^ suc a
Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → ΦSegment (f n) ν) → SNormal →^ lim f
```

```agda
Φₛ-pres-rd : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) preserves Road
Φₛ-pres : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) preserves _<_
Φₛ-pres = map Φₛ-pres-rd
```

```agda
Φ-infl≼-x0    : (λ x → ⟪ Φ {a} ν ⟫ x 0̇) inflates _≼_
Φₛ-infl≼-x0   : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) inflates _≼_
Φₛ-infl≼-bx0  : (λ x → ⟪ Φₛ {a} Φ̇ᵃ b ⟫ x 0̇) inflates _≼_
Φₗ-infl≼-x0   : ⦃ _ : wf f ⦄ {Φ̇ᶠ : ∀ {n} → ΦSegment (f n) ν} →
                (λ x → Φₗ {f} Φ̇ᶠ {n} x 0̇ ⟨ 0 ⟩) inflates _≼_
```

```agda
Φ-pres≼-x0    : (λ x → ⟪ Φ {a} ν ⟫ x 0̇) preserves _≼_
Φₛ-pres≼-x0   : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ 0 ⟩) preserves _≼_
Φₛ-pres≼-bx0  : (λ x → ⟪ Φₛ {a} Φ̇ᵃ b ⟫ x 0̇) preserves _≼_
```

```agda
Φₛ-pres≼-x0b  : (λ x → Φₛ {a} Φ̇ᵃ x 0̇ ⟨ b ⟩) preserves _≼_
Φₛ-pres≼-xb0  : (λ x → ⟪ Φₛ {a} {ν} Φ̇ᵃ x ⟫ b 0̇) preserves _≼_
```

## 主互递归构造第一部

```agda
Φ {(zero)} ν = ν
Φ {suc a} ν = Φₛ {a} (Φ ν , refl)
Φ {lim f} ν = Φₗ {f} (Φ ν , refl)
```

```agda
jumperₛ : (Φ̇ᵃ : ΦSegment a ν) (g : Seq) (w : wf g) → Jumper
jumperₛ Φ̇ᵃ g w = jumper
  (lim (λ n → Φₛ Φ̇ᵃ (g n) 0̇ ⟨ 0 ⟩) ⦃ Φₛ-pres w ⦄)
  (λ n x → ⟪ Φₛ Φ̇ᵃ (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ Φₛ-infl≼-bx0 Φₛ-pres≼-bx0 (Φₛ-pres≼-xb0 (≤→≼ (<→≤ w)))
```

```agda
Φₛ Φ̇ᵃ zero = fst Φ̇ᵃ
Φₛ Φ̇ᵃ (suc b) = Φ (fp (Φₛ Φ̇ᵃ b 0̇))
Φₛ Φ̇ᵃ (lim g) = Φ (jump (jumperₛ Φ̇ᵃ g it))
```

```agda
jumperₗₛ : (f : Seq) ⦃ _ : wf f ⦄ (Φ̇ᶠ : ∀ {n} → ΦSegment (f n) ν) (b : Ord) → Jumper
jumperₗₛ f Φ̇ᶠ b = jumper
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} Φ̇ᶠ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} Φ̇ᶠ {n} b ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!    !} {!   !} {!   !}
```

```agda
jumperₗₗ : (f : Seq) ⦃ _ : wf f ⦄ (Φ̇ᶠ : ∀ {n} → ΦSegment (f n) ν) (g : Seq) (w : wf g) → Jumper
jumperₗₗ f Φ̇ᶠ g w = jumper
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} Φ̇ᶠ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} Φ̇ᶠ {n} (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!   !} {!   !} {!   !}
```

```agda
Φₗ Φ̇ᶠ zero = fst Φ̇ᶠ
Φₗ {f} Φ̇ᶠ (suc b) = Φ (jump (jumperₗₛ f Φ̇ᶠ b))
Φₗ {f} Φ̇ᶠ (lim g) = Φ (jump (jumperₗₗ f Φ̇ᶠ g it))
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
  jump _ ⟨ 0 ⟩                          ≈⟨ Φ-0b ⟩
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

```agda
Φ-pres≼-x0 {(zero)} {ν} = Strong.pres≼ (srg ν)
Φ-pres≼-x0 {suc a} = Φₛ-pres≼-x0
Φ-pres≼-x0 {lim f} = {!   !}
```

```agda
Φₛ-pres≼-x0 {y = zero} z≼  = ≼-refl
Φₛ-pres≼-x0 {y = suc y} z≼ = subst (_ ≼_) Φ-0b $ ≼[ 1 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 {y = lim f} z≼ = subst (_ ≼_) Φ-0b $ ≼[ 0 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 {Φ̇ᵃ} (s≼s {a} {b} p) = subst₂ _≼_ Φ-0b Φ-0b $ l≼l q where
  q : Itₙ (λ _ x → Φₛ Φ̇ᵃ a 0̇ ⟨ x ⟩) 0 n ≼ Itₙ (λ _ x → Φₛ Φ̇ᵃ b 0̇ ⟨ x ⟩) 0 n
  q {(zero)} = ≼-refl
  q {suc n} =                           begin
    Φₛ Φ̇ᵃ a 0̇ ⟨ _ ⟩                     ≤⟨ Strong.pres≼ (srg (Φₛ Φ̇ᵃ a 0̇)) q ⟩
    Φₛ Φ̇ᵃ a 0̇ ⟨ _ ⟩                     ≤⟨ Φₛ-pres≼-x0b p ⟩
    Φₛ Φ̇ᵃ b 0̇ ⟨ _ ⟩                     ∎ where open CrossTreeReasoning
Φₛ-pres≼-x0 (≼l {n} p) = subst (_ ≼_) Φ-0b $ ≼[ n ] (Φₛ-pres≼-x0 p)
Φₛ-pres≼-x0 (l≼ p) = subst (_≼ _) Φ-0b $ l≼ (Φₛ-pres≼-x0 p)
```

```agda
Φₛ-pres≼-bx0 {(zero)} {Φ̇ᵃ} {b} = Strong.pres≼ (srg (Φₛ Φ̇ᵃ b))
Φₛ-pres≼-bx0 {suc a}  {Φ̇ᵃ = Φᵃ , refl} {(zero)} = Φ-pres≼-x0
Φₛ-pres≼-bx0 {lim f}  {Φ̇ᵃ = Φᵃ , refl} {(zero)} = Φ-pres≼-x0
Φₛ-pres≼-bx0 {suc a}  {Φ̇ᵃ} {suc b} = Φ-pres≼-x0
Φₛ-pres≼-bx0 {lim f}  {Φ̇ᵃ} {suc b} = Φ-pres≼-x0
Φₛ-pres≼-bx0 {suc a}  {Φ̇ᵃ} {lim g} = Φ-pres≼-x0
Φₛ-pres≼-bx0 {lim f}  {Φ̇ᵃ} {lim g} = Φ-pres≼-x0
```

## 次互递归引理第一部

```agda
Φ-pres≼-νb0   : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → ∀ {b} → ⟪ Φ {a} ν₁ ⟫ b 0̇ ≼ ⟪ Φ {a} ν₂ ⟫ b 0̇
Φₛ-pres≼-νb0c : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → ∀ {c} → Φₛ {a} {ν₁} Φ̇ᵃ₁ b 0̇ ⟨ c ⟩ ≼ Φₛ {a} {ν₂} Φ̇ᵃ₂ b 0̇ ⟨ c ⟩
Φₛ-pres≼-νbc0 : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → ∀ {b c} → ⟪ Φₛ {a} {ν₁} Φ̇ᵃ₁ b ⟫ c 0̇ ≼ ⟪ Φₛ {a} {ν₂} Φ̇ᵃ₂ b ⟫ c 0̇
```

```agda
Φ-pres≼-νb0 {a = zero} p = p
Φ-pres≼-νb0 {a = suc a} p = Φₛ-pres≼-νb0c p
Φ-pres≼-νb0 {a = lim f} p = {!   !}
```

```agda
Φₛ-pres≼-νb0c {Φ̇ᵃ₁ = _ , refl} {b = zero} {Φ̇ᵃ₂ = _ , refl} p = subst₂ _≼_ Φ-0b Φ-0b $ p
Φₛ-pres≼-νb0c {b = suc b} p = subst₂ _≼_ Φ-0b Φ-0b $ fp-pres≼ (Φₛ _ b 0̇) (Φₛ _ b 0̇) $ Φₛ-pres≼-νb0c p
Φₛ-pres≼-νb0c {b = lim f} p = subst₂ _≼_ Φ-0b Φ-0b $ jump-pres≼ (l≼l $ Φₛ-pres≼-νb0c p)
  λ {n} {x} {y} q →                     begin
  ⟪ Φₛ _ (f n) ⟫ x 0̇                    ≤⟨ Φₛ-pres≼-bx0 q ⟩
  ⟪ Φₛ _ (f n) ⟫ y 0̇                    ≤⟨ Φₛ-pres≼-νbc0 p ⟩
  ⟪ Φₛ _ (f n) ⟫ y 0̇                    ∎ where open CrossTreeReasoning
```

```agda
Φₛ-pres≼-νbc0 {Φ̇ᵃ₁ = _ , refl} {Φ̇ᵃ₂ = _ , refl} p {b = zero} = Φ-pres≼-νb0 p
Φₛ-pres≼-νbc0 p {b = suc b} = Φ-pres≼-νb0 $ fp-pres≼ (Φₛ _ b 0̇) (Φₛ _ b 0̇) $ Φₛ-pres≼-νb0c p
Φₛ-pres≼-νbc0 p {b = lim f} = Φ-pres≼-νb0 $ jump-pres≼ (l≼l $ Φₛ-pres≼-νb0c p)
  λ {n} {x} {y} q →                     begin
  ⟪ Φₛ _ (f n) ⟫ x 0̇                    ≤⟨ Φₛ-pres≼-bx0 q ⟩
  ⟪ Φₛ _ (f n) ⟫ y 0̇                    ≤⟨ Φₛ-pres≼-νbc0 p ⟩
  ⟪ Φₛ _ (f n) ⟫ y 0̇                    ∎ where open CrossTreeReasoning
```

## 次互递归引理第二部

```agda
Φ-infl≼-νx0   : ν ⟨ x ⟩ ≼ ⟪ Φ {a} ν ⟫ x 0̇
Φₛ-infl≼-νx0   : ν ⟨ x ⟩ ≼ Φₛ {a} {ν} Φ̇ᵃ x 0̇ ⟨ 0 ⟩
Φₛ-infl≼-νb0x  : ν ⟨ x ⟩ ≼ Φₛ {a} {ν} Φ̇ᵃ b 0̇ ⟨ x ⟩
Φₛ-infl≼-νbx0  : Φₛ {a} Φ̇ᵃ b 0̇ ⟨ x ⟩ ≼ ⟪ Φₛ {a} Φ̇ᵃ b ⟫ x 0̇
```

```agda
Φ-infl≼-νx0 {a = zero}  = ≼-refl
Φ-infl≼-νx0 {a = suc a} = Φₛ-infl≼-νx0
Φ-infl≼-νx0 {a = lim f} = {!   !}
```

```agda
Φₛ-infl≼-νx0 {ν} {(zero)} {Φ̇ᵃ = _ , refl} = subst (_ ≼_) Φ-0b ≼-refl
Φₛ-infl≼-νx0 {ν} {suc x} =                    begin
  ν ⟨ suc x ⟩                                 ≤⟨ Strong.pres≼ (srg ν) Φₛ-Φₛ-infl≺ ⟩
  ν ⟨ Φₛ _ x 0̇ ⟨ Φₛ _ x 0̇ ⟨ 0 ⟩ ⟩ ⟩           ≤⟨ Φₛ-infl≼-νb0x ⟩
  Φₛ _ x 0̇ ⟨ Φₛ _ x 0̇ ⟨ Φₛ _ x 0̇ ⟨ 0 ⟩ ⟩ ⟩    ≤⟨ f≼l {n = 3} ⟩
  fp (Φₛ _ x 0̇) ⟨ 0 ⟩                         ≈⟨ ≡→≈ Φ-0b ⟩
  Φ (fp (Φₛ _ x 0̇)) 0̇ ⟨ 0 ⟩                   ∎ where open CrossTreeReasoning
Φₛ-infl≼-νx0 {ν} {lim f} = subst (_ ≼_) Φ-0b $ begin
  ν ⟨ lim f ⟩                                 ≈⟨ Normal.continuous (nml $ ν) ⟩
  lim- (λ n → ν ⟨ f n ⟩)                      ≤⟨ l≼l Φₛ-infl≼-νx0 ⟩
  lim- (λ n → Φₛ _ (f n) 0̇ ⟨ 0 ⟩)             ∎ where open CrossTreeReasoning
```

```agda
Φₛ-infl≼-νb0x {Φ̇ᵃ = _ , refl} {b = zero} = subst (_ ≼_) Φ-0b $ ≼-refl
Φₛ-infl≼-νb0x {b = suc b} = subst (_ ≼_) Φ-0b $ ≼-trans Φₛ-infl≼-νb0x (fp-infl≼ (Φₛ _ b 0̇))
Φₛ-infl≼-νb0x {ν} {(zero)} {Φ̇ᵃ} {b = lim g} = subst (_ ≼_) Φ-0b $ ≼[ 0 ] Φₛ-infl≼-νb0x
Φₛ-infl≼-νb0x {ν} {suc x}  {Φ̇ᵃ} {b = lim g} = subst (_ ≼_) Φ-0b $ ≼[ 1 ] $ begin
  ν ⟨ suc x ⟩                                 ≤⟨ Φₛ-infl≼-νb0x ⟩
  Φₛ Φ̇ᵃ (g 0) 0̇ ⟨ suc x ⟩                     ≤⟨ Strong.pres≼ (srg $ Φₛ _ _ 0̇) $ s≼s $ Strong.infl≼ (srg $ jump _) ⟩
  Φₛ _ (g 0) 0̇ ⟨ suc (jump _ ⟨ x ⟩ ) ⟩        ≤⟨ Φₛ-infl≼-νbx0 ⟩
  ⟪ Φₛ _ (g 0) ⟫ (suc (jump _ ⟨ x ⟩ )) 0̇      ≤⟨ a+-infl≼ ⟩
  suc _ + ⟪ Φₛ Φ̇ᵃ (g 0) ⟫ (suc _) 0̇           ∎ where open CrossTreeReasoning
Φₛ-infl≼-νb0x {ν} {lim f}  {Φ̇ᵃ} {b = lim g} = begin
  ν ⟨ lim f ⟩                                 ≈⟨ Normal.continuous (nml $ ν) ⟩
  lim- (λ n → ν ⟨ f n ⟩)                      ≤⟨ l≼l $ Φₛ-infl≼-νb0x {Φ̇ᵃ = Φ̇ᵃ} {lim g} ⟩
  lim- (λ n → Φ (jump _) 0̇ ⟨ f n ⟩)           ≈˘⟨ Normal.continuous (nml $ Φ (jump _) 0̇) ⟩
  Φ (jump _) 0̇ ⟨ lim f ⟩                      ∎ where open CrossTreeReasoning
```

```agda
Φₛ-infl≼-νbx0 {Φ̇ᵃ = _ , refl} {b = zero} = subst (_≼ ⟪ Φ _ ⟫ _ 0̇) Φ-0b Φ-infl≼-νx0
Φₛ-infl≼-νbx0 {b = suc b} = subst (_≼ ⟪ Φ _ ⟫ _ 0̇) Φ-0b Φ-infl≼-νx0
Φₛ-infl≼-νbx0 {b = lim f} = subst (_≼ ⟪ Φ _ ⟫ _ 0̇) Φ-0b Φ-infl≼-νx0
```

## 主互递归构造第二部

```agda
-- these verbose `aux` indirections are due to termination checker limitation
Φₛ-pres≼-x0b-aux-0 : {w : wf g} → (∀ {x} → Φₛ {a} Φ̇ᵃ 0 0̇ ⟨ x ⟩ ≼ Φₛ Φ̇ᵃ (g 0) 0̇ ⟨ x ⟩)
                    → Φₛ Φ̇ᵃ 0 0̇ ⟨ x ⟩ ≼ Φ {a} (jump (jumperₛ Φ̇ᵃ g w)) 0̇ ⟨ x ⟩
Φₛ-pres≼-x0b-aux-0 {x = zero} p = subst (_ ≼_) Φ-0b $ ≼[ 0 ] $ p
Φₛ-pres≼-x0b-aux-0 {g} {Φ̇ᵃ} {suc x} p = subst (_ ≼_) Φ-0b $ ≼[ 1 ] $ begin
  Φₛ Φ̇ᵃ 0 0̇ ⟨ suc x ⟩                         ≤⟨ p ⟩
  Φₛ Φ̇ᵃ (g 0) 0̇ ⟨ suc x ⟩                     ≤⟨ Strong.pres≼ (srg $ Φₛ _ _ 0̇) $ s≼s $ Strong.infl≼ (srg $ jump _) ⟩
  Φₛ Φ̇ᵃ (g 0) 0̇ ⟨ suc (jump _ ⟨ x ⟩) ⟩        ≤⟨ Φₛ-infl≼-νbx0 ⟩
  ⟪ Φₛ Φ̇ᵃ (g 0) ⟫ (suc (jump _ ⟨ x ⟩)) 0̇      ≤⟨ a+-infl≼ ⟩
  suc _ + ⟪ Φₛ Φ̇ᵃ (g 0) ⟫ (suc _) 0̇           ∎ where open CrossTreeReasoning
Φₛ-pres≼-x0b-aux-0 {Φ̇ᵃ} {x = lim h} p =       begin
  Φₛ Φ̇ᵃ 0 0̇ ⟨ lim h ⟩                         ≈⟨ Normal.continuous (nml $ Φₛ Φ̇ᵃ 0 0̇) ⟩
  lim- (λ n → Φₛ Φ̇ᵃ 0 0̇ ⟨ h n ⟩)              ≤⟨ l≼l $ Φₛ-pres≼-x0b-aux-0 p ⟩
  lim- (λ n → Φ (jump _) 0̇ ⟨ h n ⟩)           ≈˘⟨ Normal.continuous (nml $ Φ (jump _) 0̇) ⟩
  Φ (jump _) 0̇ ⟨ lim h ⟩                      ∎ where open CrossTreeReasoning

Φₛ-pres≼-x0b-aux-b : {w : wf g} → (∀ {x} → Φₛ {a} Φ̇ᵃ b 0̇ ⟨ x ⟩ ≼ Φₛ Φ̇ᵃ (g n) 0̇ ⟨ x ⟩)
                    → Φₛ Φ̇ᵃ b 0̇ ⟨ x ⟩ ≼ Φ {a} (jump (jumperₛ Φ̇ᵃ g w)) 0̇ ⟨ x ⟩
Φₛ-pres≼-x0b-aux-b {n} {x = zero} p = subst (_ ≼_) Φ-0b $ ≼[ n ] p
Φₛ-pres≼-x0b-aux-b {g} {Φ̇ᵃ} {b} {n} {suc x} p = subst (_ ≼_) Φ-0b $ ≼[ suc n ] $ begin
  Φₛ Φ̇ᵃ b 0̇ ⟨ suc x ⟩                         ≤⟨ p ⟩
  Φₛ Φ̇ᵃ (g n) 0̇ ⟨ suc x ⟩                     ≤⟨ Strong.pres≼ (srg $ Φₛ _ _ 0̇) $ s≼s $ Strong.infl≼ (srg $ jump _) ⟩
  Φₛ Φ̇ᵃ (g n) 0̇ ⟨ suc (jump _ ⟨ x ⟩) ⟩        ≤⟨ Φₛ-infl≼-νbx0 ⟩
  ⟪ Φₛ Φ̇ᵃ (g n) ⟫ (suc (jump _ ⟨ x ⟩)) 0̇      ≤⟨ a+-infl≼ ⟩
  It (jumperₛ Φ̇ᵃ g _) x n + _                 ≤⟨ a+-infl≼ ⟩
  suc _ + It (jumperₛ Φ̇ᵃ g _) x (suc n)       ∎ where open CrossTreeReasoning
Φₛ-pres≼-x0b-aux-b {Φ̇ᵃ} {b} {x = lim h} p =   begin
  Φₛ Φ̇ᵃ b 0̇ ⟨ lim h ⟩                         ≈⟨ Normal.continuous (nml $ Φₛ Φ̇ᵃ b 0̇) ⟩
  lim- (λ n → Φₛ Φ̇ᵃ b 0̇ ⟨ h n ⟩)              ≤⟨ l≼l $ Φₛ-pres≼-x0b-aux-b p ⟩
  lim- (λ n → Φ (jump _) 0̇ ⟨ h n ⟩)           ≈˘⟨ Normal.continuous (nml $ Φ (jump _) 0̇) ⟩
  Φ (jump _) 0̇ ⟨ lim h ⟩                      ∎ where open CrossTreeReasoning
```

```agda
Φₛ-pres≼-x0b {y = zero} z≼ = ≼-refl
Φₛ-pres≼-x0b {b} {y = suc y} z≼ =             begin
  Φₛ _ 0 0̇ ⟨ b ⟩                              ≤⟨ Φₛ-pres≼-x0b z≼ ⟩
  Φₛ _ y 0̇ ⟨ b ⟩                              ≤⟨ fp-infl≼ (Φₛ _ y 0̇) ⟩
  fp (Φₛ _ y 0̇) ⟨ b ⟩                         ≈⟨ ≡→≈ Φ-0b ⟩
  Φ (fp (Φₛ _ y 0̇)) 0̇ ⟨ b ⟩                   ∎ where open CrossTreeReasoning
Φₛ-pres≼-x0b {y = lim g} z≼ = Φₛ-pres≼-x0b-aux-0 (Φₛ-pres≼-x0b z≼)
Φₛ-pres≼-x0b (s≼s p) = subst₂ _≼_ Φ-0b Φ-0b $ fp-pres≼ (Φₛ _ _ 0̇) (Φₛ _ _ 0̇) (Φₛ-pres≼-x0b p)
Φₛ-pres≼-x0b (≼l p) = Φₛ-pres≼-x0b-aux-b (Φₛ-pres≼-x0b p)
Φₛ-pres≼-x0b {y = zero} (l≼ {f} {w} p) = ⊥-elim $ ≺-asym (<→≺ (n<fs f 1 ⦃ w ⦄)) (s≼s p)
Φₛ-pres≼-x0b {y = suc y} (l≼ p) = subst (_≼ _) Φ-0b $ {!   !}
Φₛ-pres≼-x0b {y = lim f} (l≼ p) = subst₂ (_≼_) Φ-0b Φ-0b $ {!   !}
```

```agda
Φₛ-pres≼-xb0 {Φ̇ᵃ = _ , refl} {y = zero} z≼ = ≼-refl
Φₛ-pres≼-xb0 {Φ̇ᵃ = _ , refl} {y = suc y} z≼ = Φ-pres≼-νb0 $ ≼-trans Φₛ-infl≼-νb0x (fp-infl≼ (Φₛ _ _ 0̇))
Φₛ-pres≼-xb0 {Φ̇ᵃ = _ , refl} {y = lim f} z≼ = Φ-pres≼-νb0 {!   !}
Φₛ-pres≼-xb0 (s≼s p) = Φ-pres≼-νb0 $ fp-pres≼ (Φₛ _ _ 0̇) (Φₛ _ _ 0̇) $ Φₛ-pres≼-x0b p
Φₛ-pres≼-xb0 (≼l p) = {!   !}
Φₛ-pres≼-xb0 (l≼ p) = {!   !}
```

```agda
φ : SNormal →^ a
φ = Φ ω^
```

```agda
Γ : SNormal
Γ = φ {2} 1 0
```

```agda
SVO : Ord
SVO = φ {ω} {0} 1 ⟨ 0 ⟩
```
