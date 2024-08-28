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
  jump_ : FNormal
  jump_ = normal F⁺ F⁺-pres ≈-refl , fixable F⁺-infl≼ F⁺-pres≼ ⦃ F⁺-isLim ⦄ F⁺-absorb-n

open Jump using (jump_)
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
  ⟪⟫-nz {(zero)} {b} {νᵃ} = Normal.nz (fst νᵃ)
  ⟪⟫-nz {suc a} {b} {νᵃ} = Normal.nz (fst $ νᵃ b 0̇)
  ⟪⟫-nz {lim f} {b} {νᵃ} = Normal.nz (fst $ νᵃ b 0̇)
```

```agda
private variable
  ν ν₁ ν₂ : FNormal
  νᵃ : FNormal →^ a
```

```agda
Φₛ : FNormal →^ a → FNormal →^ suc a
Φₗ : ⦃ _ : wf f ⦄ → (∀ {n} → FNormal →^ f n) → FNormal →^ lim f
Φ  : FNormal → (∀ {a} → FNormal →^ a)
```

```agda
Φₛ-pres-rd : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) preserves Road
Φₛ-pres : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) preserves _<_
Φₛ-pres = map Φₛ-pres-rd
```

```agda
Φ-infl≼-x0 : (λ x → ⟪ Φ ν {a} ⟫ x 0̇) inflates _≼_
Φₛ-infl≼-x0 : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) inflates _≼_
Φₛ-infl≼-bx : (λ x → ⟪ Φₛ {a} νᵃ b ⟫ x 0̇) inflates _≼_
Φₗ-infl≼-x0 : ⦃ _ : wf f ⦄ {νᶠ : ∀ {n} → FNormal →^ f n} →
           (λ x → Φₗ {f} νᶠ {n} x 0̇ ⟨ 0 ⟩) inflates _≼_
```

```agda
Φ-pres≼-x0 : (λ x → ⟪ Φ ν {a} ⟫ x 0̇) preserves _≼_
Φₛ-pres≼-x0 : (λ x → Φₛ {a} νᵃ x 0̇ ⟨ 0 ⟩) preserves _≼_
Φₛ-pres≼-bx : (λ x → ⟪ Φₛ {a} νᵃ b ⟫ x 0̇) preserves _≼_
```

```agda
Φₛ-pres≼-xb : (λ x → ⟪ Φₛ {a} νᵃ x ⟫ b 0̇) preserves _≼_
```

```agda
Φₛ {a} νᵃ zero = νᵃ
Φₛ {a} νᵃ (suc b) = Φ (fp (Φₛ νᵃ b 0̇))
Φₛ {a} νᵃ (lim g) = Φ $ jump by
  (lim (λ n → Φₛ νᵃ (g n) 0̇ ⟨ 0 ⟩) ⦃ Φₛ-pres it ⦄)
  (λ n x → ⟪ Φₛ νᵃ (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ Φₛ-infl≼-bx Φₛ-pres≼-bx (Φₛ-pres≼-xb (≤→≼ (<→≤ it)))
```

```agda
Φₗ {f} νᶠ zero = νᶠ

Φₗ {f} νᶠ (suc b) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᶠ {n} b ⟫ 1 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} νᶠ {n} b ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!    !} {!   !} {!   !}

Φₗ {f} νᶠ (lim g) = Φ $ jump by
  (lim (Itₙ (λ n x → x + ⟪ Φₗ {f} νᶠ {n} (g n) ⟫ 0 0̇) 0) ⦃ +-infl ⦃ ⟪⟫-nz ⦄ ⦄)
  (λ n x → ⟪ Φₗ {f} νᶠ {n} (g n) ⟫ x 0̇)
  ⦃ _ ⦄ ⦃ ⟪⟫-nz ⦄ {!   !} {!   !} {!   !}
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
Φₛ-pres-rd {νᵃ} {x} zero =              begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ νᵃ x 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ νᵃ x 0̇ ⟨ Φₛ νᵃ x 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ νᵃ x 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
  Φₛ νᵃ (suc x) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {νᵃ} {x} (suc {b} r) =       begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ νᵃ b 0̇ ⟨ 0 ⟩                       <⟨ set $ Normal.pres (fst $ Φₛ νᵃ b 0̇) (nz-elim ⦃ ⟪⟫-nz {b = 0} ⦄) ⟩
  Φₛ νᵃ b 0̇ ⟨ Φₛ νᵃ b 0̇ ⟨ 0 ⟩ ⟩         <⟨ f<l-rd {n = 2} ⟩
  fp (Φₛ νᵃ b 0̇) ⟨ 0 ⟩                  ≈˘⟨ Φ-ż ⟩
  Φₛ νᵃ (suc b) 0̇ ⟨ 0 ⟩                 ∎ where open RoadReasoning
Φₛ-pres-rd {νᵃ} {x} (lim {f} {n} r) =   begin-strict
  Φₛ νᵃ x 0̇ ⟨ 0 ⟩                       <⟨ Φₛ-pres-rd r ⟩
  Φₛ νᵃ (f n) 0̇ ⟨ 0 ⟩                   <⟨ f<l-rd ⟩
  (jump _) ⟨ 0 ⟩                        ≈˘⟨ Φ-ż ⟩
  Φ (jump _) 0̇ ⟨ 0 ⟩                    ∎ where open RoadReasoning
```

```agda
Φ-infl≼-x0{ν} {(zero)} = Fixable.infl≼ (fixbl ν)
Φ-infl≼-x0{ν} {suc a} = Φₛ-infl≼-x0
Φ-infl≼-x0{ν} {lim f} = Φₗ-infl≼-x0
```

```agda
Φₛ-infl≼-x0 {νᵃ} {(zero)} = z≼
Φₛ-infl≼-x0 {νᵃ} {suc x} = subst (suc x ≼_) (sym Φ-ż) $ ≼[ 2 ] $ begin
  suc x                                   ≤⟨ s≼s Φₛ-infl≼-x0 ⟩
  suc (Φₛ νᵃ x 0̇ ⟨ 0 ⟩)                   ≤⟨ <→≺ (pres (nz-elim ⦃ zero-nz ⦄)) ⟩
  Φₛ νᵃ x 0̇ ⟨ Φₛ νᵃ x 0̇ ⟨ 0 ⟩ ⟩           ∎ where open CrossTreeReasoning; open Normal (nml $ Φₛ νᵃ x 0̇)
Φₛ-infl≼-x0 {νᵃ} {lim f} = subst (lim f ≼_) (sym Φ-ż) (l≼l Φₛ-infl≼-x0)
```

```agda
Φₛ-infl≼-bx {(zero)}  {νᵃ} {(zero)} = Fixable.infl≼ (fixbl νᵃ)
Φₛ-infl≼-bx {(zero)}  {νᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx {(zero)}  {νᵃ} {lim f}  = Φ-infl≼-x0
Φₛ-infl≼-bx {suc a}   {νᵃ} {(zero)} = {!   !}
Φₛ-infl≼-bx {suc a}   {νᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx {suc a}   {νᵃ} {lim g}  = Φ-infl≼-x0
Φₛ-infl≼-bx {lim f}   {νᵃ} {(zero)} = {!   !}
Φₛ-infl≼-bx {lim f}   {νᵃ} {suc b}  = Φ-infl≼-x0
Φₛ-infl≼-bx {lim f}   {νᵃ} {lim g}  = Φ-infl≼-x0
```

```agda
Φₗ-infl≼-x0 {νᶠ} {(zero)} = z≼
Φₗ-infl≼-x0 {νᶠ} {suc x} = subst (suc x ≼_) (sym Φ-ż) $ ≼[ 1 ] {!   !}
Φₗ-infl≼-x0 {νᶠ} {lim f} = subst (lim f ≼_) (sym Φ-ż) (l≼l {!   !})
```

```agda
Φ-pres≼-x0 {ν} {(zero)} = Fixable.pres≼ (fixbl ν)
Φ-pres≼-x0 {ν} {suc a} = Φₛ-pres≼-x0
Φ-pres≼-x0 {ν} {lim f} = {!   !}
```

```agda
Φₛ-pres≼-x0 {y = zero} z≼ = ≼-refl
Φₛ-pres≼-x0 {y = suc y} z≼ = subst (_ ≼_) (sym Φ-ż) $ ≼[ 1 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 {y = lim f} z≼ = subst (_ ≼_) (sym Φ-ż) $ ≼[ 0 ] $ Φₛ-pres≼-x0 z≼
Φₛ-pres≼-x0 (s≼s p) = subst₂ _≼_ (sym Φ-ż) (sym Φ-ż) $ l≼l $
  λ { {(zero)} → ≼-refl ; {suc n} → {!   !} }
Φₛ-pres≼-x0 (≼l p) = {!   !}
Φₛ-pres≼-x0 (l≼ x) = {!   !}
```

```agda
Φₛ-pres≼-bx {(zero)} {νᵃ} {b} p = Fixable.pres≼ (fixbl (Φₛ νᵃ b)) p
Φₛ-pres≼-bx {suc a} {νᵃ} {(zero)} p = {!   !}
Φₛ-pres≼-bx {suc a} {νᵃ} {suc b} = Φ-pres≼-x0
Φₛ-pres≼-bx {suc a} {νᵃ} {lim f} = Φ-pres≼-x0
Φₛ-pres≼-bx {lim f} = {!   !}
```

```agda
Φₛ-pres≼-xb {b = zero} p = Φₛ-pres≼-x0 p
Φₛ-pres≼-xb {b = suc b} {y = zero} z≼ = {!   !}
Φₛ-pres≼-xb {b = suc b} {y = suc y} z≼ = {!   !}
Φₛ-pres≼-xb {b = suc b} {y = lim f} z≼ = {!   !}
Φₛ-pres≼-xb {b = suc b} (s≼s p) = {!   !}
Φₛ-pres≼-xb {b = suc b} (≼l p) = {!   !}
Φₛ-pres≼-xb {b = suc b} (l≼ x) = {!   !}
Φₛ-pres≼-xb {b = lim f} p = {!   !}
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
