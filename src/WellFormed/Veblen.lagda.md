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

**定义 2-5-xx** 高阶强正规函数

```agda
record Higher (νᵃ : SNormal →^ a) : Type where
  constructor higher
  field
    infl≼ : (λ x → ⟪ νᵃ ⟫ x 0̇) inflates _≼_
    pres≼ : (λ x → ⟪ νᵃ ⟫ x 0̇) preserves _≼_

HigherSNormal : Ord → Type
HigherSNormal a = Σ (SNormal →^ a) (Higher {a})

sn : HigherSNormal a → SNormal →^ a
sn = fst

hi : ((νᵃ , _) : HigherSNormal a) → Higher νᵃ
hi = snd
```

```agda
private variable
  ν ν₁ ν₂ : SNormal
  νᵃ : SNormal →^ a
  ν̇ᵃ ν̇ᵃ₁ ν̇ᵃ₂ : HigherSNormal a
```

```agda
Φₛ : HigherSNormal a → SNormal →^ suc a
Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → HigherSNormal (f n)) → SNormal →^ lim f
Φ  : SNormal → (∀ {a} → SNormal →^ a)
Φ-higher : Higher {a} (Φ ν)
```

```agda
Φₛ-pres-rd : (λ x → Φₛ {a} ν̇ᵃ x 0̇ ⟨ 0 ⟩) preserves Road
Φₛ-pres : (λ x → Φₛ {a} ν̇ᵃ x 0̇ ⟨ 0 ⟩) preserves _<_
Φₛ-pres = map Φₛ-pres-rd
```

```agda
Φ-infl≼-x0    : (λ x → ⟪ Φ ν {a} ⟫ x 0̇) inflates _≼_
Φₛ-infl≼-x0   : (λ x → Φₛ {a} ν̇ᵃ x 0̇ ⟨ 0 ⟩) inflates _≼_
Φₛ-infl≼-bx0  : (λ x → ⟪ Φₛ {a} ν̇ᵃ b ⟫ x 0̇) inflates _≼_
Φₗ-infl≼-x0   : ⦃ _ : wf f ⦄ {ν̇ᶠ : ∀ {n} → HigherSNormal (f n)} →
                (λ x → Φₗ {f} ν̇ᶠ {n} x 0̇ ⟨ 0 ⟩) inflates _≼_
```

```agda
Φ-pres≼-x0    : (λ x → ⟪ Φ ν {a} ⟫ x 0̇) preserves _≼_
Φₛ-pres≼-x0   : (λ x → Φₛ {a} ν̇ᵃ x 0̇ ⟨ 0 ⟩) preserves _≼_
Φₛ-pres≼-bx0  : (λ x → ⟪ Φₛ {a} ν̇ᵃ b ⟫ x 0̇) preserves _≼_
```

```agda
Φ-pres≼-νb0   : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → ∀ {b} → ⟪ Φ ν₁ {a} ⟫ b 0̇ ≼ ⟪ Φ ν₂ {a} ⟫ b 0̇
-- `Φ ν₁ {suc a} b 0̇ ⟨ c ⟩ ≼ Φ ν₂ {suc a} b 0̇ ⟨ c ⟩` and
-- `⟪ Φ ν₁ {suc a} b ⟫ c 0̇ ≼ ⟪ Φ ν₂ {suc a} b ⟫ c 0`
-- has to be writen as below due to termination checker limitation
Φₛ-pres≼-νb0c : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → (∀ {c} → Φₛ {a} (Φ ν₁ , Φ-higher) b 0̇ ⟨ c ⟩ ≼ Φₛ {a} (Φ ν₂ , Φ-higher) b 0̇ ⟨ c ⟩)
Φₛ-pres≼-νbc0 : (∀ {b} → ν₁ ⟨ b ⟩ ≼ ν₂ ⟨ b ⟩) → (∀ {b c} → ⟪ Φₛ {a} (Φ ν₁ , Φ-higher) b ⟫ c 0̇ ≼ ⟪ Φₛ {a} (Φ ν₂ , Φ-higher) b ⟫ c 0̇)
```

```agda
Φₛ-pres≼-x0b  : (λ x → Φₛ {a} ν̇ᵃ x 0̇ ⟨ b ⟩) preserves _≼_
Φₛ-pres≼-xb0  : (λ x → ⟪ Φₛ {a} ν̇ᵃ x ⟫ b 0̇) preserves _≼_
```

```agda
Φₛ {a} ν̇ᵃ zero = sn ν̇ᵃ
Φₛ {a} ν̇ᵃ (suc b) = Φ (fp (Φₛ ν̇ᵃ b 0̇))
Φₛ {a} ν̇ᵃ (lim g) = Φ $ jump by
  (lim (λ n → Φₛ ν̇ᵃ (g n) 0̇ ⟨ 0 ⟩) ⦃ Φₛ-pres it ⦄)
  (λ n x → ⟪ Φₛ ν̇ᵃ (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ Φₛ-infl≼-bx0 Φₛ-pres≼-bx0 (Φₛ-pres≼-xb0 (≤→≼ (<→≤ it)))
```

```agda
Φₗ {f} ν̇ᶠ zero = sn ν̇ᶠ

Φₗ {f} ν̇ᶠ (suc b) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} ν̇ᶠ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} ν̇ᶠ {n} b ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!    !} {!   !} {!   !}

Φₗ {f} ν̇ᶠ (lim g) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} ν̇ᶠ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} ν̇ᶠ {n} (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!   !} {!   !} {!   !}
```

```agda
Φ ν {(zero)} = ν
Φ ν {suc a} = Φₛ {a} (Φ ν , Φ-higher)
Φ ν {lim f} = Φₗ {f} (Φ ν , Φ-higher)
```

```agda
Φ-higher {(zero)} {ν} = higher infl≼ pres≼ where open Strong (srg ν)
Φ-higher {suc a} = higher Φₛ-infl≼-x0 Φₛ-pres≼-x0
Φ-higher {lim f} = higher Φₗ-infl≼-x0 {!   !}
```

```agda
Φ-0b : Φ ν {a} 0̇ ⟨ b ⟩ ≡ ν ⟨ b ⟩
Φ-0b {a = zero} = refl
Φ-0b {a = suc a} = Φ-0b {a = a}
Φ-0b {a = lim f} = Φ-0b {a = f 0}
```

```agda
Φₛ-pres-rd {ν̇ᵃ} {x} zero =              begin-strict
  Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ ν̇ᵃ x 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ ν̇ᵃ x 0̇ ⟨ Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ ν̇ᵃ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-0b ⟩
  Φₛ ν̇ᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {ν̇ᵃ} {x} (suc {b} r) =       begin-strict
  Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ ν̇ᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ ν̇ᵃ b 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ ν̇ᵃ b 0̇ ⟨ Φₛ ν̇ᵃ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ ν̇ᵃ b 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-0b ⟩
  Φₛ ν̇ᵃ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {ν̇ᵃ} {x} (lim {f} {n} r) =   begin-strict
  Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ ν̇ᵃ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
  (jump _) ⟨ 0 ⟩                        ≈˘⟨ Φ-0b ⟩
  Φ (jump _) 0̇ ⟨ 0 ⟩                    ∎ where open RoadReasoning
```

```agda
Φ-infl≼-x0 {ν} {(zero)} = Strong.infl≼ (srg ν)
Φ-infl≼-x0 {ν} {suc a} = Φₛ-infl≼-x0
Φ-infl≼-x0 {ν} {lim f} = Φₗ-infl≼-x0
```

```agda
Φₛ-infl≼-x0 {ν̇ᵃ} {(zero)} = z≼
Φₛ-infl≼-x0 {ν̇ᵃ} {suc x} = subst (suc x ≼_) (sym Φ-0b) $ ≼[ 2 ] $ begin
  suc x                                 ≤⟨ s≼s Φₛ-infl≼-x0 ⟩
  suc (Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩)                 ≤⟨ <→≺ (pres (nz-elim ⦃ zero-nz ⦄)) ⟩
  Φₛ ν̇ᵃ x 0̇ ⟨ Φₛ ν̇ᵃ x 0̇ ⟨ 0 ⟩ ⟩         ∎ where open CrossTreeReasoning; open Normal (nml $ Φₛ ν̇ᵃ x 0̇)
Φₛ-infl≼-x0 {ν̇ᵃ} {lim f} = subst (lim f ≼_) (sym Φ-0b) $ l≼l Φₛ-infl≼-x0
```

```agda
Φₛ-infl≼-bx0 {(zero)}  {ν̇ᵃ} {(zero)} = Strong.infl≼ (srg (sn ν̇ᵃ))
Φₛ-infl≼-bx0 {(zero)}  {ν̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {(zero)}  {ν̇ᵃ} {lim f}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {suc a}   {ν̇ᵃ} {(zero)} = Higher.infl≼ (hi ν̇ᵃ)
Φₛ-infl≼-bx0 {suc a}   {ν̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {suc a}   {ν̇ᵃ} {lim g}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {lim f}   {ν̇ᵃ} {(zero)} = Higher.infl≼ (hi ν̇ᵃ)
Φₛ-infl≼-bx0 {lim f}   {ν̇ᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx0 {lim f}   {ν̇ᵃ} {lim g}  = Φ-infl≼-x0
```

```agda
Φₗ-infl≼-x0 {ν̇ᶠ} {(zero)} = z≼
Φₗ-infl≼-x0 {ν̇ᶠ} {suc x} = subst (suc x ≼_) (sym Φ-0b) $ ≼[ 1 ] $ {!   !}
Φₗ-infl≼-x0 {ν̇ᶠ} {lim f} = subst (lim f ≼_) (sym Φ-0b) $ l≼ls $ ≼-trans Φₗ-infl≼-x0 a+-infl≼
```

```agda
Φ-pres≼-x0 {ν} {(zero)} = Strong.pres≼ (srg ν)
Φ-pres≼-x0 {ν} {suc a}  = Φₛ-pres≼-x0
Φ-pres≼-x0 {ν} {lim f}  = {!   !}
```

```agda
Φₛ-pres≼-x0 {y = zero} z≼  = ≼-refl
Φₛ-pres≼-x0 {y = suc y} z≼ = subst (_ ≼_) (sym Φ-0b) $ ≼[ 1 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 {y = lim f} z≼ = subst (_ ≼_) (sym Φ-0b) $ ≼[ 0 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 {ν̇ᵃ} (s≼s {a} {b} p) = subst₂ _≼_ (sym Φ-0b) (sym Φ-0b) $ l≼l q where
  q : Itₙ (λ _ x → Φₛ ν̇ᵃ a 0̇ ⟨ x ⟩) 0 n ≼ Itₙ (λ _ x → Φₛ ν̇ᵃ b 0̇ ⟨ x ⟩) 0 n
  q {(zero)} = ≼-refl
  q {suc n} =                           begin
    Φₛ ν̇ᵃ a 0̇ ⟨ _ ⟩                     ≤⟨ Strong.pres≼ (srg (Φₛ ν̇ᵃ a 0̇)) q ⟩
    Φₛ ν̇ᵃ a 0̇ ⟨ _ ⟩                     ≤⟨ Φₛ-pres≼-x0b p ⟩
    Φₛ ν̇ᵃ b 0̇ ⟨ _ ⟩                     ∎ where open CrossTreeReasoning
Φₛ-pres≼-x0 (≼l {n} p) = subst (_ ≼_) (sym Φ-0b) $ ≼[ n ] (Φₛ-pres≼-x0 p)
Φₛ-pres≼-x0 (l≼ p) = subst (_≼ _) (sym Φ-0b) $ l≼ (Φₛ-pres≼-x0 p)
```

```agda
Φₛ-pres≼-bx0 {(zero)} {ν̇ᵃ} {b}      = Strong.pres≼ (srg (Φₛ ν̇ᵃ b))
Φₛ-pres≼-bx0 {suc a}  {ν̇ᵃ} {(zero)} = Higher.pres≼ (hi ν̇ᵃ)
Φₛ-pres≼-bx0 {suc a}  {ν̇ᵃ} {suc b}  = Φ-pres≼-x0
Φₛ-pres≼-bx0 {suc a}  {ν̇ᵃ} {lim g}  = Φ-pres≼-x0
Φₛ-pres≼-bx0 {lim f}  {ν̇ᵃ} {(zero)} = Higher.pres≼ (hi ν̇ᵃ)
Φₛ-pres≼-bx0 {lim f}  {ν̇ᵃ} {suc b}  = Φ-pres≼-x0
Φₛ-pres≼-bx0 {lim f}  {ν̇ᵃ} {lim g}  = Φ-pres≼-x0
```

```agda
Φ-pres≼-νb0 {a = zero} p = p
Φ-pres≼-νb0 {a = suc a} p = Φₛ-pres≼-νb0c p
Φ-pres≼-νb0 {a = lim f} p = {!   !}
```

```agda
Φₛ-pres≼-νb0c {b = zero} p  = subst₂ _≼_ (sym Φ-0b) (sym Φ-0b) $ p
Φₛ-pres≼-νb0c {b = suc b} p = subst₂ _≼_ (sym Φ-0b) (sym Φ-0b) $ fp-pres≼ (Φₛ _ b 0̇) (Φₛ _ b 0̇) $ Φₛ-pres≼-νb0c p
Φₛ-pres≼-νb0c {ν₁} {ν₂} {a} {lim f} p = subst₂ _≼_ (sym Φ-0b) (sym Φ-0b) $ jump-pres≼ (l≼l $ Φₛ-pres≼-νb0c p)
  λ {n} {x} {y} q →                     begin
  ⟪ Φₛ (Φ ν₁ , Φ-higher) (f n) ⟫ x 0̇    ≤⟨ Φₛ-pres≼-bx0 q ⟩
  ⟪ Φₛ (Φ ν₁ , Φ-higher) (f n) ⟫ y 0̇    ≤⟨ Φₛ-pres≼-νbc0 p ⟩
  ⟪ Φₛ (Φ ν₂ , Φ-higher) (f n) ⟫ y 0̇    ∎ where open CrossTreeReasoning
```

```agda
Φₛ-pres≼-νbc0 p {(zero)}  = Φ-pres≼-νb0 p
Φₛ-pres≼-νbc0 p {suc b}   = Φ-pres≼-νb0 $ fp-pres≼ (Φₛ _ b 0̇) (Φₛ _ b 0̇) $ Φₛ-pres≼-νb0c p
Φₛ-pres≼-νbc0 {ν₁} {ν₂} p {lim f} = Φ-pres≼-νb0 $ jump-pres≼ (l≼l $ Φₛ-pres≼-νb0c p)
  λ {n} {x} {y} q →                     begin
  ⟪ Φₛ (Φ ν₁ , Φ-higher) (f n) ⟫ x 0̇    ≤⟨ Φₛ-pres≼-bx0 q ⟩
  ⟪ Φₛ (Φ ν₁ , Φ-higher) (f n) ⟫ y 0̇    ≤⟨ Φₛ-pres≼-νbc0 p ⟩
  ⟪ Φₛ (Φ ν₂ , Φ-higher) (f n) ⟫ y 0̇    ∎ where open CrossTreeReasoning
```

```agda
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {b} {y = zero}  z≼ = ≼-refl
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {b} {y = suc y} z≼ = begin
  Φₛ {a} ν̇ᵃ 0 0̇ ⟨ b ⟩                   ≤⟨ Φₛ-pres≼-x0b z≼ ⟩
  Φₛ {a} ν̇ᵃ y 0̇ ⟨ b ⟩                   ≤⟨ fp-infl≼ (Φₛ {a} ν̇ᵃ y 0̇) ⟩
  fp (Φₛ ν̇ᵃ y 0̇) ⟨ b ⟩                  ≈˘⟨ ≡→≈ Φ-0b ⟩
  Φ (fp (Φₛ ν̇ᵃ y 0̇)) 0̇ ⟨ b ⟩            ∎ where open CrossTreeReasoning

Φₛ-pres≼-x0b {a} {ν̇ᵃ} {(zero)} {y = lim g} z≼ =
  subst (_ ≼_) (sym Φ-0b) $ ≼[ 0 ] $ Φₛ-pres≼-x0b z≼
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {suc b}  {y = lim g} z≼ =
  subst (_ ≼_) (sym Φ-0b) $ ≼[ 1 ] $ {!   !}
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {lim f}  {y = lim g} z≼ =
  subst (_ ≼_) (sym Φ-0b) $             begin
  Φₛ {a} ν̇ᵃ 0 0̇ ⟨ lim f ⟩               ≈⟨ Normal.continuous (nml $ sn ν̇ᵃ 0̇) ⟩
  lim- (λ n → Φₛ {a} ν̇ᵃ 0 0̇ ⟨ f n ⟩)    ≤⟨ l≼l p ⟩
  (jump _) ⟨ lim f ⟩                    ∎ where
  open CrossTreeReasoning
  p = λ {n} →                           begin
    Φₛ {a} ν̇ᵃ 0 0̇ ⟨ f n ⟩               ≤⟨ {! Φₛ-pres≼-x0b {y = lim g} z≼  !} ⟩
    Φ (jump _) {a} 0̇ ⟨ f n ⟩            ≈⟨ ≡→≈ Φ-0b ⟩
    (jump _) ⟨ f n ⟩                    ∎

Φₛ-pres≼-x0b {a} {ν̇ᵃ} {b} (s≼s p) = subst₂ _≼_ (sym Φ-0b) (sym Φ-0b) $
  fp-pres≼ (Φₛ _ _ 0̇) (Φₛ _ _ 0̇) (Φₛ-pres≼-x0b p)
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {b} (≼l p) = {!   !}
Φₛ-pres≼-x0b {a} {ν̇ᵃ} {b} (l≼ p) = {!   !}
```
Φₛ {a} ν̇ᵃ 0 0̇ ⟨ suc b ⟩
suc (jump _) ⟨ b ⟩ + ⟪ Φₛ ν̇ᵃ (g 0) ⟫ (suc (jump _) ⟨ b ⟩) 0̇

```agda
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} {y = zero}  z≼ = ≼-refl
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} {y = suc y} z≼ = {!   !}
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} {y = lim f} z≼ = {!   !}
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} (s≼s p) = Φ-pres≼-νb0 $ fp-pres≼ (Φₛ ν̇ᵃ _ 0̇) (Φₛ ν̇ᵃ _ 0̇) (Φₛ-pres≼-x0b p)
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} (≼l p) = {!   !}
Φₛ-pres≼-xb0 {a} {ν̇ᵃ} {b} (l≼ x) = {!   !}
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
 