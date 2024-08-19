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
continuous : {F : Func} → F preserves _<_ → Type
continuous {F} pres = ∀ {f} {w : wf f} → F (lim f ⦃ w ⦄) ≡ lim (F ∘ f) ⦃ pres w ⦄
```

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
    nml-cont : continuous nml-pres
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
    lim- (F ∘ Iₙ F 0)       ≈˘⟨ ≡→≈ nml-cont ⟩
    F lfp                   ∎ where open CrossTreeReasoning
```

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

```agda
module Fixpt (ℱ : Normal) where
  open Normal ℱ renaming (_⟨_⟩ to F)

  wₛ : wf (Iₙ (λ x → suc a + F x) (suc a))
  wₛ {n = zero} = +-infl
  wₛ {n = suc n} = +-pres (nml-pres wₛ)

  fixpt : Normal
  fixpt = jump 0 F Iₙ zero lfp-wf wₛ

open Fixpt public using (fixpt)
open Normal public
```

```agda
module _ {ℱ : Normal} where
  fixpt-fix : fixpt ℱ ⟨ a ⟩ ≈ ℱ ⟨ fixpt ℱ ⟨ a ⟩ ⟩
  fixpt-fix {a = zero}  = lfp-fix ℱ
  fixpt-fix {a = suc a} = {!   !}
  fixpt-fix {a = lim f} =   begin-equality
    fixpt ℱ ⟨ lim f ⟩       ≈⟨ l≈l fixpt-fix ⟩
    lim- (λ n → ℱ ⟨ _ ⟩)    ≈˘⟨ ≡→≈ (nml-cont ℱ) ⟩
    ℱ ⟨ fixpt ℱ ⟨ lim f ⟩ ⟩ ∎ where open CrossTreeReasoning
```

```agda
ω^ : Normal
ω^ = normal (ω ^_) ^-pres refl
```

```agda
ε ζ η : Normal
ε = fixpt ω^
ζ = fixpt ε
η = fixpt ζ
```
