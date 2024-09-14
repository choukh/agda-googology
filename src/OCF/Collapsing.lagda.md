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

## 非零序数

```agda
nonZero : Ord a → Type
nonZero zero = ⊥
nonZero _ = ⊤

record NonZero (α : Ord a) : Type where
  field .wrap : nonZero α
```

```agda
z<s : Wf α → 0 <ₐ suc α
z≤  : Wf α → 0 ≤ α

z<l : Wf (f 0) → {w : wf f} → 0 <ₐ lim f ⦃ w ⦄
z<l {f} W =               begin-strict
  0                       ≤⟨ z≤ W ⟩
  f 0                     <⟨ f<l ⟩
  lim- f                  ∎ where open HigherRoadReasoning

z<L : Wf (F (elm 0)) → Pres _ F → 0 <ₐ Lim aℓ F
z<L {F} W F-Pres =        begin-strict
  0                       ≤⟨ z≤ W ⟩
  F (elm 0)               <⟨ Lim (F-Pres zero) ⟩
  Lim _ F                 ∎ where open HigherRoadReasoning

z<s zero           = zero
z<s (suc α̇)        = suc (z<s α̇)
z<s (lim ḟ)        = suc (z<l ḟ)
z<s (Lim Ḟ F-pres) = suc (z<L (Ḟ {0}) F-pres)

z≤ zero            = inr refl
z≤ (suc α̇)         = inl (z<s α̇)
z≤ (lim ḟ)         = inl (z<l ḟ)
z≤ (Lim Ḟ F-pres)  = inl (z<L (Ḟ {0}) F-pres)
```

```agda
nz-elim : NonZero α → Wf α → 0 < α
nz-elim _ (suc α̇)        = z<s α̇
nz-elim _ (lim ḟ)        = z<l ḟ
nz-elim _ (Lim Ḟ F-pres) = z<L (Ḟ {0}) F-pres
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
+-infl : NonZero α → Wf α → β < β + α
+-infl {β} _ (suc {α} α̇) = begin-strict
  β                       ≤⟨ +-infl≤ α̇ ⟩
  β + α                   <⟨ +-pres zero ⟩
  β + suc α               ∎ where open HigherRoadReasoning
+-infl {β} _ (lim {f} ḟ) = begin-strict
  β                       ≤⟨ +-infl≤ ḟ ⟩
  β + f 0                 <⟨ +-pres f<l ⟩
  β + lim- f              ∎ where open HigherRoadReasoning
+-infl {β} _ (Lim {aℓ} {F} Ḟ F-pres) = begin-strict
  β                       ≤⟨ +-infl≤ (Ḟ {0}) ⟩
  β + F (elm 0)           <⟨ +-pres $ Lim $ F-pres zero ⟩
  β + Lim aℓ F            ∎ where open HigherRoadReasoning
```

```agda
+α-id : 0 + α ≡ α
+α-id {α = zero} = refl
+α-id {α = suc α} = cong suc +α-id
+α-id {α = lim f} = limExt λ _ → +α-id
+α-id {α = Lim _ F} = LimExt refl λ _ → +α-id
{-# REWRITE +α-id #-}
```

## 序数崩塌函数

```agda
lfp : (F : Ord a → Ord a) → NonZero (F 0) → Wf (F 0) → F preserves _<_ → Ord a
lfp F nz W pres = lim (λ n → (F ∘ⁿ n) 0) ⦃ w ⦄ where
  w : wf (λ n → (F ∘ⁿ n) 0)
  w {(zero)} = ∣ nz-elim nz W ∣₁
  w {suc n} = map pres w
```

```agda
ψₐ : a ⊏ ℓ → Ord ℓ → Ord a
ψₐ-pres : {aℓ : a ⊏ ℓ} → β < γ → ψₐ aℓ β < ψₐ aℓ γ
ψₐ-nz : NonZero (ψₐ aℓ α)
ψₐ-Wf : Wf (ψₐ aℓ α)

ψₐ aℓ zero          = lfp (Ω _ +_)      Ω-nz Ω-Wf   +-pres
ψₐ aℓ (suc α)       = lfp (ψₐ aℓ α +_)  ψₐ-nz ψₐ-Wf +-pres
ψₐ aℓ (lim f)       = lim (ψₐ aℓ ∘ f) ⦃ map ψₐ-pres it ⦄
ψₐ aℓ (Lim {a = b} bℓ F) rewrite Elm≡Ord {aℓ = bℓ} with ⊏-trich aℓ bℓ
... | tri< a⊏b _ _  = lfp (λ x → ψₐ aℓ (F $ lift a⊏b x)) ψₐ-nz ψₐ-Wf λ x → ψₐ-pres {!   !}
... | tri≈ _ refl _ = lfp (λ x → ψₐ aℓ (F x))            ψₐ-nz ψₐ-Wf λ x → ψₐ-pres {!   !}
... | tri> _ _ b⊏a  = Lim b⊏a λ x → ψₐ aℓ (F $ ord x)

ψₐ-pres zero = lim {n = 2} (+-infl ψₐ-nz ψₐ-Wf)
ψₐ-pres (suc r) = lim {n = 1} (ψₐ-pres r)
ψₐ-pres f<l = f<l
ψₐ-pres (lim {n} r) = lim {n = n} (ψₐ-pres r)
ψₐ-pres (Lim r) = {!   !}

ψₐ-nz {α = zero}  = _
ψₐ-nz {α = suc α} = _
ψₐ-nz {α = lim f} = _
ψₐ-nz {aℓ} {α = Lim bℓ F} rewrite Elm≡Ord {aℓ = bℓ} with ⊏-trich aℓ bℓ
... | tri< _ _ _    = _
... | tri≈ _ refl _ = _
... | tri> _ _ _    = _

ψₐ-Wf = {!   !}
```

```agda
ψ : ∀ ℓ → Ord ℓ → Ord 0
ψ-nz : NonZero (ψ ℓ α)
ψ-Wf : Wf (ψ ℓ α)

ψ zero α = suc α
ψ (suc ℓ) α = ψ ℓ (ψₐ zero α)
ψ (lim f) α = lim (Itₙ (λ n x → x + ψ (f n) (ψₐ f⊏l α)) 0) ⦃ w ⦄ where
  w : wf (Itₙ (λ n x → x + ψ (f n) (ψₐ f⊏l α)) 0)
  w {(zero)} = ∣ nz-elim ψ-nz ψ-Wf ∣₁
  w {suc n}  = ∣ +-infl ψ-nz ψ-Wf ∣₁

ψ-nz {(zero)} = _
ψ-nz {suc ℓ} = ψ-nz {ℓ}
ψ-nz {lim f} = _

ψ-Wf = {!   !}
```

## 本方法的极限

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
ψ-Ω_Ω : PlainOrd
ψ-Ω_Ω = plainLim ψₙ

ψ-Ω_Ω-99 : ℕ
ψ-Ω_Ω-99 = FGH.f ψ-Ω_Ω 99
```
