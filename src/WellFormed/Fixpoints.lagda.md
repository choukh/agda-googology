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

  F⁺-pres-rd zero         = rd[ 0 ] infl
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ rd-trans (F⁺-pres-rd r) infl
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r

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
module FixpointsProperties {ℱ : Normal}
  (ℱ-infl≼ : (ℱ ⟨_⟩) inflates _≼_)
  (ℱ-pres≼ : (ℱ ⟨_⟩) preserves _≼_)
  (ℱ-absorb-1 : ∀ {a} → 0 < a → 1 + ℱ ⟨ a ⟩ ≈ ℱ ⟨ a ⟩)
  (ℱ-absorb-≺ : ∀ {a b} → a ≺ b → ℱ ⟨ a ⟩ + ℱ ⟨ b ⟩ ≈ ℱ ⟨ b ⟩)
  where
```

```agda
  ℱ-cong≈ : a ≈ b → ℱ ⟨ a ⟩ ≈ ℱ ⟨ b ⟩
  ℱ-cong≈ (p , q) = ℱ-pres≼ p , ℱ-pres≼ q
```

```agda
  fp-fix : fp ℱ ⟨ a ⟩ ≈ ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩
  fp-suc-[n] : fp ℱ ⟨ suc a ⟩ [ n ] ≈ Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n
```

```agda
  fp-fix {a = zero}  = lfp-fix ℱ
  fp-fix {a = suc a} = p , q where
    open CrossTreeReasoning
    p =                                     begin
      fp ℱ ⟨ suc a ⟩                        ≤⟨ l≼l ℱ-infl≼ ⟩
      lim- (λ n → ℱ ⟨ _ ⟩)                  ≈˘⟨ ≡→≈ (continuous ℱ) ⟩
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ ⟩                  ∎
    q[n] = λ {n} →                          begin
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩            ≈⟨ ℱ-cong≈ fp-suc-[n] ⟩
      ℱ ⟨ Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n ⟩ ≈⟨ ≈-refl ⟩
      Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) (suc n) ≈˘⟨ fp-suc-[n] ⟩
      fp ℱ ⟨ suc a ⟩ [ suc n ]              ∎
    q =                                     begin
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ ⟩                  ≈⟨ ≡→≈ (continuous ℱ) ⟩
      lim- (λ n → ℱ ⟨ _ ⟩)                  ≤⟨ l≼ls q[n] ⟩
      fp ℱ ⟨ suc a ⟩                        ∎
  fp-fix {a = lim f} =                      begin-equality
    fp ℱ ⟨ lim f ⟩                          ≈⟨ l≈l fp-fix ⟩
    lim- (λ n → ℱ ⟨ _ ⟩)                    ≈˘⟨ ≡→≈ (continuous ℱ) ⟩
    ℱ ⟨ fp ℱ ⟨ lim f ⟩ ⟩                    ∎ where open CrossTreeReasoning
```

```agda
  fp-suc-[0] : fp ℱ ⟨ suc a ⟩ [ 0 ] ≡ suc (fp ℱ ⟨ a ⟩)
  fp-suc-[0] = refl
```

```agda
  fp-suc-[s] : fp ℱ ⟨ suc a ⟩ [ suc n ] ≈ ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩
  fp-suc-[s] {a} {n} =                      begin-equality
    fp ℱ ⟨ suc a ⟩ [ suc n ]                ≈⟨ ≈-refl ⟩
    suc (fp ℱ ⟨ a ⟩) + ℱ ⟨ _ ⟩              ≈⟨ +a-cong≈ (s≈s fp-fix) ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + 1 + ℱ ⟨ _ ⟩          ≈˘⟨ ≡→≈ +-assoc ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + (1 + ℱ ⟨ _ ⟩)        ≈⟨ a+-cong≈ (ℱ-absorb-1 p) ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + ℱ ⟨ _ ⟩              ≈⟨ ℱ-absorb-≺ (<→≺ q) ⟩
    ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩              ∎ where
    open CrossTreeReasoning
    p : 0 < fp ℱ ⟨ suc a ⟩ [ m ]
    p {(zero)} = z<s
    p {suc m} = <-trans z<s (+-infl ⦃ nml-nz ℱ ⦄)
    q : fp ℱ ⟨ a ⟩ < fp ℱ ⟨ suc a ⟩ [ m ]
    q {(zero)} = zero₁
    q {suc m} = <-trans q (Fixpoints.wₛ ℱ)
```

```agda
  fp-suc-[n] {n = zero} = ≡→≈ fp-suc-[0]
  fp-suc-[n] {a} {n = suc n} =              begin-equality
    fp ℱ ⟨ suc a ⟩ [ suc n ]                ≈⟨ fp-suc-[s] ⟩
    ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩              ≈⟨ ℱ-cong≈ fp-suc-[n] ⟩
    ℱ ⟨ Iₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n ⟩   ∎ where open CrossTreeReasoning
```

```agda
  fp-infl≼ : (fp ℱ ⟨_⟩) inflates _≼_
  fp-infl≼ {(zero)} = z≼
  fp-infl≼ {suc _}  = ≼l {n = 0} (s≼s fp-infl≼)
  fp-infl≼ {lim f}  = l≼l fp-infl≼
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
  fp-absorb-1 : 0 < a → 1 + fp ℱ ⟨ a ⟩ ≈ fp ℱ ⟨ a ⟩
  fp-absorb-1 {(zero)} _ = 1+l-absorb
  fp-absorb-1 {suc a} _  = 1+l-absorb
  fp-absorb-1 {lim f} _  = 1+l-absorb
```

```agda
  fp-absorb-≺ : a ≺ b → fp ℱ ⟨ a ⟩ + fp ℱ ⟨ b ⟩ ≈ fp ℱ ⟨ b ⟩
  fp-absorb-≺ {a} {b = suc b} (s≼s a≼b) =
    (l≼ λ {n} →                                     begin
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]             ≤⟨ +a-pres≼ (fp-pres≼ a≼b) ⟩
      fp ℱ ⟨ b ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]             ≤⟨ +a-pres≼ ≼-zero ⟩
      suc (fp ℱ ⟨ b ⟩) + fp ℱ ⟨ suc b ⟩ [ n ]       ≤⟨ a+-pres≼ ℱ-infl≼ ⟩
      suc (fp ℱ ⟨ b ⟩) + ℱ ⟨ fp ℱ ⟨ suc b ⟩ [ n ] ⟩ ≈⟨ ≈-refl ⟩
      fp ℱ ⟨ suc b ⟩ [ suc n ]                      ≤⟨ f≼l {n = suc n} ⟩
      fp ℱ ⟨ suc b ⟩                                ∎) ,
    (l≼ λ {n} →                                     begin
      fp ℱ ⟨ suc b ⟩ [ n ]                          ≤⟨ a+-infl≼ ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]             <⟨ a+-pres≺ (<→≺ (Fixpoints.wₛ ℱ)) ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ suc n ]         ≤⟨ f≼l {n = suc n} ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩                   ∎) where
    open CrossTreeReasoning
  fp-absorb-≺ {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
    open CrossTreeReasoning
    aux : fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f m ⟩ ≼ lim- (λ m → fp ℱ ⟨ f m ⟩)
    aux {m} with <-cmp n m
    ... | tri< n<m _ _  = {!   !}
    ... | tri≈ _ refl _ = {!   !}
    ... | tri> _ _ m<n  = {!   !}
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
