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

## 不动点的枚举

```agda
module FpEnum (ν : Normal) where
  open Normal using (_⟨_⟩)
  open Normal ν

  sfp-wf : wf (Itₙ (λ x → suc a + ν ⟨ x ⟩) (suc a))
  sfp-wf {n = zero} = +-infl
  sfp-wf {n = suc n} = +-pres (nml-pres sfp-wf)

  F′ : Func
  F′-pres-rd : F′ preserves Road
  F′-pres : F′ preserves _<_
  F′-pres = map F′-pres-rd

  F′ zero = lfp
  F′ (suc a) = let j = suc (F′ a) in
               lim (λ n → Itₙ (λ x → j + ν ⟨ x ⟩) j n) ⦃ sfp-wf ⦄
  F′ (lim f) = lim (F′ ∘ f) ⦃ F′-pres it ⦄

  F′-pres-rd zero = rd[ 0 ] zero
  F′-pres-rd (suc r) = rd[ 0 ] $ rd-trans (F′-pres-rd r) zero
  F′-pres-rd (lim {n} r)  = rd[ n ] $ F′-pres-rd r

  fp : Normal
  fp = normal F′ F′-pres refl

open FpEnum public using (fp; sfp-wf)
open Normal public
```

### 跨树性质

```agda
record Fixable (ν : Normal) : Type where
  constructor fixable
  field
    fixbl-infl≼ : (ν ⟨_⟩) inflates _≼_
    fixbl-pres≼ : (ν ⟨_⟩) preserves _≼_
    fixbl-isLim : ∀ {a} → NonZero a → isLim (ν ⟨ a ⟩)
    fixbl-absorb : ∀ {a b} → a ≺ b → ν ⟨ a ⟩ + ν ⟨ b ⟩ ≈ ν ⟨ b ⟩

  fixbl-cong≈ : a ≈ b → ν ⟨ a ⟩ ≈ ν ⟨ b ⟩
  fixbl-cong≈ (p , q) = fixbl-pres≼ p , fixbl-pres≼ q
```

```agda
  fp-fix : fp ν ⟨ a ⟩ ≈ ν ⟨ fp ν ⟨ a ⟩ ⟩
  fp-suc-[n] : fp ν ⟨ suc a ⟩ [ n ] ≈ Itₙ (ν ⟨_⟩) (suc (fp ν ⟨ a ⟩)) n
```

```agda
  fp-fix {a = zero}  = lfp-fix ν
  fp-fix {a = suc a} = p , q where
    open CrossTreeReasoning
    p =                                       begin
      fp ν ⟨ suc a ⟩                          ≤⟨ l≼l fixbl-infl≼ ⟩
      lim- (λ n → ν ⟨ _ ⟩)                    ≈˘⟨ ≡→≈ (continuous ν) ⟩
      ν ⟨ fp ν ⟨ suc a ⟩ ⟩                    ∎
    q[n] = λ {n} →                            begin
      ν ⟨ fp ν ⟨ suc a ⟩ [ n ] ⟩              ≈⟨ fixbl-cong≈ fp-suc-[n] ⟩
      ν ⟨ Itₙ (ν ⟨_⟩) (suc (fp ν ⟨ a ⟩)) n ⟩  ≈⟨ ≈-refl ⟩
      Itₙ (ν ⟨_⟩) (suc (fp ν ⟨ a ⟩)) (suc n)  ≈˘⟨ fp-suc-[n] ⟩
      fp ν ⟨ suc a ⟩ [ suc n ]                ∎
    q =                                       begin
      ν ⟨ fp ν ⟨ suc a ⟩ ⟩                    ≈⟨ ≡→≈ (continuous ν) ⟩
      lim- (λ n → ν ⟨ _ ⟩)                    ≤⟨ l≼ls q[n] ⟩
      fp ν ⟨ suc a ⟩                          ∎
  fp-fix {a = lim f} =                        begin-equality
    fp ν ⟨ lim f ⟩                            ≈⟨ l≈l fp-fix ⟩
    lim- (λ n → ν ⟨ _ ⟩)                      ≈˘⟨ ≡→≈ (continuous ν) ⟩
    ν ⟨ fp ν ⟨ lim f ⟩ ⟩                      ∎ where open CrossTreeReasoning
```

```agda
  fp-suc-[0] : fp ν ⟨ suc a ⟩ [ 0 ] ≡ suc (fp ν ⟨ a ⟩)
  fp-suc-[0] = refl
```

```agda
  fp-suc-[s] : fp ν ⟨ suc a ⟩ [ suc n ] ≈ ν ⟨ fp ν ⟨ suc a ⟩ [ n ] ⟩
  fp-suc-[s] {a} {n} =                        begin-equality
    fp ν ⟨ suc a ⟩ [ suc n ]                  ≈⟨ ≈-refl ⟩
    suc (fp ν ⟨ a ⟩) + ν ⟨ _ ⟩                ≈⟨ +a-cong≈ (s≈s fp-fix) ⟩
    ν ⟨ fp ν ⟨ a ⟩ ⟩ + 1 + ν ⟨ _ ⟩            ≈˘⟨ ≡→≈ +-assoc ⟩
    ν ⟨ fp ν ⟨ a ⟩ ⟩ + (1 + ν ⟨ _ ⟩)          ≈⟨ a+-cong≈ (1+l-absorb $ fixbl-isLim $ nz-intro p) ⟩
    ν ⟨ fp ν ⟨ a ⟩ ⟩ + ν ⟨ _ ⟩                ≈⟨ fixbl-absorb (<→≺ q) ⟩
    ν ⟨ fp ν ⟨ suc a ⟩ [ n ] ⟩                ∎ where
    open CrossTreeReasoning
    p : 0 < fp ν ⟨ suc a ⟩ [ m ]
    p {(zero)} = z<s
    p {suc m} = <-trans z<s (+-infl ⦃ nml-nz ν ⦄)
    q : fp ν ⟨ a ⟩ < fp ν ⟨ suc a ⟩ [ m ]
    q {(zero)} = zero₁
    q {suc m} = <-trans q (sfp-wf ν)
```

```agda
  fp-suc-[n] {n = zero} = ≡→≈ fp-suc-[0]
  fp-suc-[n] {a} {n = suc n} =                begin-equality
    fp ν ⟨ suc a ⟩ [ suc n ]                  ≈⟨ fp-suc-[s] ⟩
    ν ⟨ fp ν ⟨ suc a ⟩ [ n ] ⟩                ≈⟨ fixbl-cong≈ fp-suc-[n] ⟩
    ν ⟨ Itₙ (ν ⟨_⟩) (suc (fp ν ⟨ a ⟩)) n ⟩    ∎ where open CrossTreeReasoning
```

### 性质的封闭

```agda
  fp-infl≼ : (fp ν ⟨_⟩) inflates _≼_
  fp-infl≼ {(zero)} = z≼
  fp-infl≼ {suc _}  = ≼l {n = 0} (s≼s fp-infl≼)
  fp-infl≼ {lim f}  = l≼l fp-infl≼
```

```agda
  fp-pres≼ : (fp ν ⟨_⟩) preserves _≼_
  fp-pres≼ {y = zero}  z≼ = ≼-refl
  fp-pres≼ {y = suc y} z≼ = ≼l {n = 0} (≼-suc (fp-pres≼ z≼))
  fp-pres≼ {y = lim f} z≼ = ≼l {n = 0} (fp-pres≼ z≼)
  fp-pres≼ (≼l {n} p)     = ≼l {n = n} (fp-pres≼ p)
  fp-pres≼ (l≼ p)         = l≼ (fp-pres≼ p)
  fp-pres≼ (s≼s {a} {b} p) = l≼l q where
    q : fp ν ⟨ suc a ⟩ [ n ] ≼ fp ν ⟨ suc b ⟩ [ n ]
    q {n = zero} = s≼s (fp-pres≼ p)
    q {n = suc n} = +-pres≼ (s≼s (fp-pres≼ p)) (fixbl-pres≼ q)
```

```agda
  fp-cong≈ : a ≈ b → fp ν ⟨ a ⟩ ≈ fp ν ⟨ b ⟩
  fp-cong≈ (p , q) = fp-pres≼ p , fp-pres≼ q
```

```agda
  fp-isLim : NonZero a → isLim (fp ν ⟨ a ⟩)
  fp-isLim {(zero)} _ = _
  fp-isLim {suc a} _  = _
  fp-isLim {lim f} _  = _
```

```agda
  fp-absorb : a ≺ b → fp ν ⟨ a ⟩ + fp ν ⟨ b ⟩ ≈ fp ν ⟨ b ⟩
  fp-absorb {a} {b = suc b} (s≼s a≼b) =
    (l≼ λ {n} →                               begin
      fp ν ⟨ a ⟩ + fp ν ⟨ suc b ⟩ [ n ]       ≤⟨ +a-pres≼ (fp-pres≼ a≼b) ⟩
      fp ν ⟨ b ⟩ + fp ν ⟨ suc b ⟩ [ n ]       ≤⟨ +a-pres≼ ≼-zero ⟩
      suc (fp ν ⟨ b ⟩) + fp ν ⟨ suc b ⟩ [ n ] ≤⟨ a+-pres≼ fixbl-infl≼ ⟩
      suc (fp ν ⟨ b ⟩) + ν ⟨ _ ⟩              ≈⟨ ≈-refl ⟩
      fp ν ⟨ suc b ⟩ [ suc n ]                ≤⟨ f≼l {n = suc n} ⟩
      fp ν ⟨ suc b ⟩                          ∎) ,
    (l≼ λ {n} →                               begin
      fp ν ⟨ suc b ⟩ [ n ]                    ≤⟨ a+-infl≼ ⟩
      fp ν ⟨ a ⟩ + fp ν ⟨ suc b ⟩ [ n ]       <⟨ a+-pres≺ (<→≺ (sfp-wf ν)) ⟩
      fp ν ⟨ a ⟩ + fp ν ⟨ suc b ⟩ [ suc n ]   ≤⟨ f≼l {n = suc n} ⟩
      fp ν ⟨ a ⟩ + fp ν ⟨ suc b ⟩             ∎) where
    open CrossTreeReasoning
  fp-absorb {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
    open CrossTreeReasoning
    aux : fp ν ⟨ a ⟩ + fp ν ⟨ f m ⟩ ≼ lim- (λ m → fp ν ⟨ f m ⟩)
    aux {m} with <-cmp n m
    ... | tri< n<m _ _ = ≼l $                 begin
      fp ν ⟨ a ⟩ + fp ν ⟨ f m ⟩               ≤⟨ fst (fp-absorb a≺fm) ⟩
      fp ν ⟨ f m ⟩                            ∎ where
      a≺fm =                                  begin-strict
        a                                     <⟨ a≺fn ⟩
        f n                                   <⟨ <→≺ (seq-pres n<m) ⟩
        f m                                   ∎
    ... | tri≈ _ refl _ = ≼l $                begin
      fp ν ⟨ a ⟩ + fp ν ⟨ f n ⟩               ≤⟨ fst (fp-absorb a≺fn) ⟩
      fp ν ⟨ f n ⟩                            ∎
    ... | tri> _ _ m<n = ≼l $                 begin
      fp ν ⟨ a ⟩ + fp ν ⟨ f m ⟩               ≤⟨ a+-pres≼ (fp-pres≼ fm≼fn) ⟩
      fp ν ⟨ a ⟩ + fp ν ⟨ f n ⟩               ≤⟨ fst (fp-absorb a≺fn) ⟩
      fp ν ⟨ f n ⟩                            ∎ where
      fm≼fn =                                 begin
        f m                                   <⟨ <→≺ (seq-pres m<n) ⟩
        f n                                   ∎
```

```agda
fp-fixbl : ∀ {ν} → Fixable ν → Fixable (fp ν)
fp-fixbl fixbl = fixable fp-infl≼ fp-pres≼ fp-isLim fp-absorb
  where open Fixable fixbl
```

## 不动点的实例

```agda
ω^ : Normal
ω^ = normal (ω ^_) ^-pres refl
```

```agda
ω^-isLim : NonZero a → isLim (ω ^ a)
ω^-isLim {suc a} _ = _
ω^-isLim {lim f} _ = _
```

```agda
ω^-fixbl : Fixable ω^
ω^-fixbl = fixable a^-infl≼ a^-pres≼ ω^-isLim ω^-absorb
```

```agda
ε ζ η : Normal
ε = fp ω^
ζ = fp ε
η = fp ζ
```

```agda
ε-fixbl : Fixable ε
ε-fixbl = fp-fixbl ω^-fixbl

ζ-fixbl : Fixable ζ
ζ-fixbl = fp-fixbl ε-fixbl

η-fixbl : Fixable η
η-fixbl = fp-fixbl ζ-fixbl
```

```agda
η-0 : η ⟨ 0 ⟩ ≡ lim- (Itₙ (ζ ⟨_⟩) 0)
η-0 = refl

η-suc : η ⟨ suc a ⟩ ≡ lim- (Itₙ (λ x → suc (η ⟨ a ⟩) + ζ ⟨ x ⟩) (suc (η ⟨ a ⟩)))
η-suc = refl

η-lim : ⦃ _ : wf f ⦄ → η ⟨ lim f ⟩ ≡ lim- λ n → η ⟨ f n ⟩
η-lim = refl
```

```agda
η-fix : η ⟨ a ⟩ ≈ ζ ⟨ η ⟨ a ⟩ ⟩
η-fix = Fixable.fp-fix ζ-fixbl

η-suc-[n] : η ⟨ suc a ⟩ [ n ] ≈ Itₙ (ζ ⟨_⟩) (suc (η ⟨ a ⟩)) n
η-suc-[n] = Fixable.fp-suc-[n] ζ-fixbl
```

## 二元Veblen函数

```agda
module BinaryVeblenAux (ν : Normal) where

  Φ : Ord → Normal
  Φ-nz : NonZero (Φ a ⟨ b ⟩)
  instance _ = Φ-nz

  Φ-pres-rd : ∀ {x y} → Road x y → Road a (Φ y ⟨ a ⟩) → Road (Φ x ⟨ a ⟩) (Φ y ⟨ a ⟩)
  Φ-pres : ∀ {x y} → x < y → a < Φ y ⟨ a ⟩ → Φ x ⟨ a ⟩ < Φ y ⟨ a ⟩
  Φ-pres = map2 Φ-pres-rd
```

```agda
  module Jump (f : Seq) ⦃ w : wf f ⦄ where
    h : Ord → Seq
    h a zero    = a
    h a (suc n) = h a n + Φ (f n) ⟨ a ⟩
```

```agda
    F⁺ : Func
    F⁺-pres-rd : F⁺ preserves Road
    F⁺-pres : F⁺ preserves _<_
    F⁺-pres = map F⁺-pres-rd
```

```agda
    F⁺ zero     = lim (λ n → Φ (f n) ⟨ 0 ⟩) ⦃ Φ-pres it nz-elim ⦄
    F⁺ (suc a)  = lim (Itₙ (λ x → x + {!   !}) (suc (F⁺ a))) ⦃ {!   !} ⦄
    F⁺ (lim g)  = lim (F⁺ ∘ g) ⦃ F⁺-pres it ⦄
```

```agda
    F⁺-pres-rd zero = {!   !}
    F⁺-pres-rd (suc r) = {!   !}
    F⁺-pres-rd (lim r) = {!   !}
```

```agda
    jump : Normal
    jump = normal F⁺ F⁺-pres refl
  open Jump public using (jump)
```

```agda
  Φ zero = ν
  Φ (suc a) = fp (Φ a)
  Φ (lim f) = jump f
```

```agda
  Φ-nz {(zero)} = nml-nz ν
  Φ-nz {suc a}  = nml-nz (fp (Φ a))
  Φ-nz {lim f}  = nml-nz (jump f)
```

```agda
  Φ-pres-rd = {!   !}
```

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
               lim (λ n → Gₙ (λ x → j + (Fₙ n) x) j n) ⦃ wₛ ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄

  F⁺-pres-rd zero         = rd[ 0 ] infl
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ rd-trans (F⁺-pres-rd r) infl
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r

  jump : Normal
  jump = normal F⁺ F⁺-pres refl

open Jump public using (jump)
```
