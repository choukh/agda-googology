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
Itₙ : Func → Ord → Seq
Itₙ F i n = (F ∘ⁿ n) i
```

```agda
record Normal : Type where
  constructor normal
  field _⟨_⟩ : Func
  private F = _⟨_⟩
  field
    nml-pres : F preserves _<_
    continuous : ∀ {f} {w : wf f} → F (lim f ⦃ w ⦄) ≡ lim (F ∘ f) ⦃ nml-pres w ⦄
    ⦃ nml-zero-nz ⦄ : NonZero (F 0)

  instance
    nml-nz : NonZero (F a)
    nml-nz {(zero)} = it
    nml-nz {suc a} = nz-intro $ begin-strict
      0                     ≤⟨ z≤ ⟩
      F _                   <⟨ nml-pres zero₁ ⟩
      F (suc _)             ∎ where open SubTreeReasoning
    nml-nz {lim f} = nz-intro $ begin-strict
      0                     <⟨ nz-elim ⟩
      F (f 0)               <⟨ nml-pres f<l ⟩
      F (lim _)             ∎ where open SubTreeReasoning

    lfp-wf : wf (Itₙ F 0)
    lfp-wf {(zero)} = nz-elim
    lfp-wf {suc n} = nml-pres lfp-wf

  lfp : Ord
  lfp = lim (Itₙ F 0)

  lfp-fix : lfp ≈ F lfp
  lfp-fix =                 begin-equality
    lfp                     ≈⟨ l≈ls ⟩
    lim- (F ∘ Itₙ F 0)      ≈˘⟨ ≡→≈ continuous ⟩
    F lfp                   ∎ where open CrossTreeReasoning
```

## 跳出运算

```agda
module Jump (i : Ord) (Fₙ : ℕ → Func) (Gₙ : Func → Ord → Seq)
  (infl : ∀ {a} → Road a (Gₙ (λ x → suc a + Fₙ 0 x) (suc a) 0))
  (w₀ : wf λ n → Gₙ (Fₙ n) i n)
  where

  F⁺ : Func
  wₛ : let j = suc (F⁺ a) in wf (λ n → Gₙ (λ x → j + Fₙ n x) j n)
  wₛ = {!   !}

  F⁺-pres-rd : F⁺ preserves Road
  F⁺-pres : F⁺ preserves _<_
  F⁺-pres = map F⁺-pres-rd

  F⁺ zero    = lim (λ n → Gₙ (Fₙ n) i n) ⦃ w₀ ⦄
  F⁺ (suc a) = let j = suc (F⁺ a) in
               lim (λ n → Gₙ (λ x → j + (Fₙ n) x) j n) ⦃ {!   !} ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄

  F⁺-pres-rd zero         = rd[ 0 ] infl
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ rd-trans (F⁺-pres-rd r) infl
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r

  jump : Normal
  jump = normal F⁺ F⁺-pres refl

open Jump public using (jump)
```
