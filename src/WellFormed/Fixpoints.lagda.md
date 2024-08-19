---
title: 形式化大数数学 (2.4 - 不动点)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.4 - 不动点)

> 交流Q群: 893531731  
> 本文源码: [Fixpoints.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Fixpoints.lagda.md)  
> 高亮渲染: [Fixpoints.html](https://choukh.github.io/agda-googology/WellFormed.Fixpoints.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
open import WellFormed.CrossTree
```

## 不动点定理

```agda
open import Lower using (_∘ⁿ_)
Iₙ : Func → Ord → Seq
Iₙ F i n = (F ∘ⁿ n) i
```

```agda
record Normal : Type where
  constructor normal
  field _⟨_⟩ : Func
  private F = _⟨_⟩
  field
    nml-pres : F preserves _<_
    continuous : ∀ {f} {w : wf f} → F (lim f ⦃ w ⦄) ≡ lim (F ∘ f) ⦃ nml-pres w ⦄
    ⦃ nml-nz ⦄ : NonZero (F 0)

  instance
    nml-suc-nz : NonZero (F (suc a))
    nml-suc-nz = nz-intro $ begin-strict
      0                     ≤⟨ z≤ ⟩
      F _                   <⟨ nml-pres zero₁ ⟩
      F (suc _)             ∎ where open SubTreeReasoning

    lfp-wf : wf (Iₙ F 0)
    lfp-wf {(zero)} = nz-elim
    lfp-wf {suc n} = nml-pres lfp-wf

  lfp : Ord
  lfp = lim (Iₙ F 0)

  lfp-fix : lfp ≈ F lfp
  lfp-fix =                 begin-equality
    lfp                     ≈⟨ l≈ls z≼ ⟩
    lim- (F ∘ Iₙ F 0)       ≈˘⟨ ≡→≈ continuous ⟩
    F lfp                   ∎ where open CrossTreeReasoning
```

## 跳出运算

```agda
module Jump (i : Ord) (F : Func) (Gₙ : Func → Ord → Seq)
  (infl : ∀ {a} → Road a (Gₙ (λ x → suc a + F x) (suc a) 0))
  (w₀ : wf (Gₙ F i)) (wₛ : ∀ {a} → wf (Gₙ (λ x → suc a + F x) (suc a)))
  where

  F⁺ : Func
  F⁺-pres-rd : F⁺ preserves Road
  F⁺-pres : F⁺ preserves _<_
  F⁺-pres = map F⁺-pres-rd

  F⁺ zero    = lim (Gₙ F i) ⦃ w₀ ⦄
  F⁺ (suc a) = let j = suc (F⁺ a) in
               lim (Gₙ (λ x → j + F x) j) ⦃ wₛ ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄

  F⁺-pres-rd zero = rd[ 0 ] infl
  F⁺-pres-rd (suc r) = rd[ 0 ] $ rd-trans (F⁺-pres-rd r) infl
  F⁺-pres-rd (lim {n} r) = rd[ n ] $ F⁺-pres-rd r

  jump : Normal
  jump = normal F⁺ F⁺-pres refl

open Jump public using (jump)
```

## 不动点的枚举

```agda
module Fixpoints (ℱ : Normal) where
  open Normal ℱ renaming (_⟨_⟩ to F)

  wₛ : wf (Iₙ (λ x → suc a + F x) (suc a))
  wₛ {n = zero} = +-infl
  wₛ {n = suc n} = +-pres (nml-pres wₛ)

  fp : Normal
  fp = jump 0 F Iₙ zero lfp-wf wₛ

open Fixpoints public using (fp)
open Normal public
```

```agda
IsLim : Ord → Type
IsLim zero = ⊥
IsLim (suc a) = ⊥
IsLim (lim f) = ⊤
```

```agda
_[_] : (a : Ord) → ⦃ IsLim a ⦄ → Seq
_[_] (lim f) = f
```

```agda
module FixpointsProperties {ℱ : Normal} (ℱ-pres≼ : (ℱ ⟨_⟩) preserves _≼_) where
  ℱ-cong≈ : a ≈ b → ℱ ⟨ a ⟩ ≈ ℱ ⟨ b ⟩
  ℱ-cong≈ (p , q) = ℱ-pres≼ p , ℱ-pres≼ q
```

```agda
  fp-pres≼ : (fp ℱ ⟨_⟩) preserves _≼_
  fp-pres≼ {y = zero}  z≼ = ≼-refl
  fp-pres≼ {y = suc y} z≼ = ≼l {n = 0} (≼-suc (fp-pres≼ z≼))
  fp-pres≼ {y = lim f} z≼ = ≼l {n = 0} (fp-pres≼ z≼)
  fp-pres≼ (≼l {n} p)     = ≼l {n = n} (fp-pres≼ p)
  fp-pres≼ (l≼ p)         = l≼ (fp-pres≼ p)
  fp-pres≼ (s≼s {a} {b} p) = l≼l q where
    q : fp ℱ ⟨ suc a ⟩ [ n ] ≼ fp ℱ ⟨ suc b ⟩ [ n ]
    q {n = zero} = s≼s (fp-pres≼ p)
    q {n = suc n} = +-pres≼ (s≼s (fp-pres≼ p)) (ℱ-pres≼ q)
```

```agda
  fp-cong≈ : a ≈ b → fp ℱ ⟨ a ⟩ ≈ fp ℱ ⟨ b ⟩
  fp-cong≈ (p , q) = fp-pres≼ p , fp-pres≼ q
```

```agda
  fp-fix : fp ℱ ⟨ a ⟩ ≈ ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩
  fp-suc-[n] : fp ℱ ⟨ suc a ⟩ [ n ] ≈ Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n
```

```agda
  fp-fix {a = zero}  = lfp-fix ℱ
  fp-fix {a = suc a} = {!   !}
  fp-fix {a = lim f} =      begin-equality
    fp ℱ ⟨ lim f ⟩          ≈⟨ l≈l fp-fix ⟩
    lim- (λ n → ℱ ⟨ _ ⟩)    ≈˘⟨ ≡→≈ (continuous ℱ) ⟩
    ℱ ⟨ fp ℱ ⟨ lim f ⟩ ⟩    ∎ where open CrossTreeReasoning
```

```agda
  fp-suc-[0] : fp ℱ ⟨ suc a ⟩ [ 0 ] ≡ suc (fp ℱ ⟨ a ⟩)
  fp-suc-[0] = refl
```

```agda
  fp-suc-[s] : fp ℱ ⟨ suc a ⟩ [ suc n ] ≈ ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩
  fp-suc-[s] = {!   !}
```

```agda
  fp-suc-[n] {n = zero} = ≡→≈ fp-suc-[0]
  fp-suc-[n] {a} {n = suc n} =              begin-equality
    fp ℱ ⟨ suc a ⟩ [ suc n ]                ≈⟨ fp-suc-[s] ⟩
    ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩              ≈⟨ ℱ-cong≈ fp-suc-[n] ⟩
    ℱ ⟨ Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n ⟩   ∎ where open CrossTreeReasoning
```

```agda
ω^ : Normal
ω^ = normal (ω ^_) ^-pres refl
```

```agda
ε ζ η : Normal
ε = fp ω^
ζ = fp ε
η = fp ζ
```
