---
title: 形式化大数数学 (3.1 - 序数崩塌函数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.1 - 序数崩塌函数)

> 交流Q群: 893531731  
> 本文源码: [Collapsing.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/OCF/Collapsing.lagda.md)  
> 高亮渲染: [Collapsing.html](httrsps://choukh.github.io/agda-googology/OCF.Collapsing.html)  

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module OCF.Collapsing where
open import OCF.HigherOrd public
open import WellFormed.Properties using (_preserves_)
open import WellFormed.Fixpoints using (Itₙ)
```

## 一些约定

```agda
nonZero : Ord a → Type
nonZero zero = ⊥
nonZero _ = ⊤

record NonZero (α : Ord a) : Type where
  field .wrap : nonZero α
```

```agda
Ω-nz : NonZero (Ω a)
Ω-nz {(zero)} = _
Ω-nz {suc a} = _
Ω-nz {lim f} = _
```

## 高阶算术

```agda
_+_ : Ord a → Ord a → Ord a; infixl 7 _+_
+-pres : β < γ → α + β < α + γ

α + zero = α
α + suc β = suc (α + β)
α + lim f = lim (λ n → α + f n) ⦃ map +-pres it ⦄
α + Lim aℓ F = Lim aℓ (λ ι → α + F ι)

+-pres zero = zero
+-pres (suc r) = suc (+-pres r)
+-pres (lim r) = lim (+-pres r)
+-pres (Lim r) = Lim (+-pres r)
+-pres f<l = f<l
```

```agda
+-infl≤ : Wf α → β ≤ β + α
+-infl≤ zero = inr refl
+-infl≤ {β} (suc {α} α̇) = begin
  β                       ≤⟨ +-infl≤ α̇ ⟩
  β + α                   <⟨ +-pres zero ⟩
  β + suc α               ∎ where open HigherRoadReasoning
+-infl≤ {β} (lim {f} ḟ) = begin
  β                       ≤⟨ +-infl≤ ḟ ⟩
  β + f 0                 <⟨ +-pres f<l ⟩
  β + lim- f              ∎ where open HigherRoadReasoning
+-infl≤ {β} (Lim {aℓ} {F} Ḟ F-pres) = begin
  β                       ≤⟨ +-infl≤ (Ḟ {0}) ⟩
  β + F (elm 0)           <⟨ +-pres $ Lim $ F-pres zero ⟩
  β + Lim aℓ F            ∎ where open HigherRoadReasoning
```

```agda
+-infl : ⦃ _ : NonZero α ⦄ → Wf α → β < β + α
+-infl {β} (suc {α} α̇) = begin-strict
  β                       ≤⟨ +-infl≤ α̇ ⟩
  β + α                   <⟨ +-pres zero ⟩
  β + suc α               ∎ where open HigherRoadReasoning
+-infl {β} (lim {f} ḟ) = begin-strict
  β                       ≤⟨ +-infl≤ ḟ ⟩
  β + f 0                 <⟨ +-pres f<l ⟩
  β + lim- f              ∎ where open HigherRoadReasoning
+-infl {β} (Lim {aℓ} {F} Ḟ F-pres) = begin-strict
  β                       ≤⟨ +-infl≤ (Ḟ {0}) ⟩
  β + F (elm 0)           <⟨ +-pres $ Lim $ F-pres zero ⟩
  β + Lim aℓ F            ∎ where open HigherRoadReasoning
```

```agda
lfp : (F : Ord a → Ord a) → NonZero (F 0) → F preserves _<_ → Ord a
lfp F nz pres = lim (λ n → (F ∘ⁿ n) 0) ⦃ w ⦄ where
  w : wf (λ n → (F ∘ⁿ n) 0)
  w {(zero)} = {! nz  !}
  w {suc n} = map pres w
```

```agda
ψₐ : a ⊏ b → Ord b → Ord a
ψₐ-pres : {ab : a ⊏ b} → β < γ → ψₐ ab β < ψₐ ab γ

ψₐ ab zero        = lfp (Ω _ +_) Ω-nz +-pres
ψₐ ab (suc α)     = lfp (ψₐ ab α +_) {!   !} +-pres
ψₐ ab (lim f)     = lim (ψₐ ab ∘ f) ⦃ map ψₐ-pres it ⦄
ψₐ ab (Lim aℓ F)  = {!   !}

ψₐ-pres zero = lim {n = 2} {!   !}
ψₐ-pres (suc r) = lim {n = 2} {!   !}
ψₐ-pres f<l = f<l
ψₐ-pres (lim {n} r) = lim {n = n} (ψₐ-pres r)
ψₐ-pres (Lim r) = {!   !}
```

```agda
ψ : ∀ ℓ → Ord ℓ → Ord 0
ψ zero α = α
ψ (suc ℓ) α = ψ ℓ (ψₐ zero α)
ψ (lim f) α = lim (Itₙ (λ n x → x + ψ (f n) (ψₐ f⊏l α)) 0) ⦃ w ⦄ where
  w : wf (Itₙ (λ n x → x + ψ (f n) (ψₐ f⊏l α)) (finOrd 0))
  w {(zero)} = {!   !}
  w {suc n} = map (+-infl {α = ψ _ _} ⦃ {!   !} ⦄) {!   !}
```

```agda
ψₙ : ℕ → Ord 0
ψₙ zero = 0
ψₙ (suc n) = ψ (level (ψₙ n)) (Ω _)
```

```agda
open import Veblen.Base renaming (Ord to PlainOrd) using (zero; suc; lim)
module FGH = Veblen.Base.FGH

plain : Ord 0 → PlainOrd
plain zero = zero
plain (suc α) = suc (plain α)
plain (lim f) = lim (plain ∘ f)

plainLim : (ℕ → Ord 0) → PlainOrd
plainLim f = lim (plain ∘ f)
```

```agda
EBO : PlainOrd
EBO = plainLim ψₙ

ebo99 : ℕ
ebo99 = FGH.f EBO 99
```