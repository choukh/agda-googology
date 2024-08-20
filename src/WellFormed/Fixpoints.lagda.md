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

  wₛ : wf (Itₙ (λ x → suc a + F x) (suc a))
  wₛ {n = zero} = +-infl
  wₛ {n = suc n} = +-pres (nml-pres wₛ)

  fp : Normal
  fp = jump 0 F Itₙ zero lfp-wf wₛ

open Fixpoints public using (fp)
open Normal public
```

### 跨树性质

```agda
record Fixable (ℱ : Normal) : Type where
  constructor fixable
  field
    fixbl-infl≼ : (ℱ ⟨_⟩) inflates _≼_
    fixbl-pres≼ : (ℱ ⟨_⟩) preserves _≼_
    fixbl-isLim : ∀ {a} → NonZero a → isLim (ℱ ⟨ a ⟩)
    fixbl-absorb : ∀ {a b} → a ≺ b → ℱ ⟨ a ⟩ + ℱ ⟨ b ⟩ ≈ ℱ ⟨ b ⟩

  fixbl-cong≈ : a ≈ b → ℱ ⟨ a ⟩ ≈ ℱ ⟨ b ⟩
  fixbl-cong≈ (p , q) = fixbl-pres≼ p , fixbl-pres≼ q
```

```agda
  fp-fix : fp ℱ ⟨ a ⟩ ≈ ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩
  fp-suc-[n] : fp ℱ ⟨ suc a ⟩ [ n ] ≈ Itₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n
```

```agda
  fp-fix {a = zero}  = lfp-fix ℱ
  fp-fix {a = suc a} = p , q where
    open CrossTreeReasoning
    p =                                       begin
      fp ℱ ⟨ suc a ⟩                          ≤⟨ l≼l fixbl-infl≼ ⟩
      lim- (λ n → ℱ ⟨ _ ⟩)                    ≈˘⟨ ≡→≈ (continuous ℱ) ⟩
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ ⟩                    ∎
    q[n] = λ {n} →                            begin
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩              ≈⟨ fixbl-cong≈ fp-suc-[n] ⟩
      ℱ ⟨ Itₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n ⟩  ≈⟨ ≈-refl ⟩
      Itₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) (suc n)  ≈˘⟨ fp-suc-[n] ⟩
      fp ℱ ⟨ suc a ⟩ [ suc n ]                ∎
    q =                                       begin
      ℱ ⟨ fp ℱ ⟨ suc a ⟩ ⟩                    ≈⟨ ≡→≈ (continuous ℱ) ⟩
      lim- (λ n → ℱ ⟨ _ ⟩)                    ≤⟨ l≼ls q[n] ⟩
      fp ℱ ⟨ suc a ⟩                          ∎
  fp-fix {a = lim f} =                        begin-equality
    fp ℱ ⟨ lim f ⟩                            ≈⟨ l≈l fp-fix ⟩
    lim- (λ n → ℱ ⟨ _ ⟩)                      ≈˘⟨ ≡→≈ (continuous ℱ) ⟩
    ℱ ⟨ fp ℱ ⟨ lim f ⟩ ⟩                      ∎ where open CrossTreeReasoning
```

```agda
  fp-suc-[0] : fp ℱ ⟨ suc a ⟩ [ 0 ] ≡ suc (fp ℱ ⟨ a ⟩)
  fp-suc-[0] = refl
```

```agda
  fp-suc-[s] : fp ℱ ⟨ suc a ⟩ [ suc n ] ≈ ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩
  fp-suc-[s] {a} {n} =                        begin-equality
    fp ℱ ⟨ suc a ⟩ [ suc n ]                  ≈⟨ ≈-refl ⟩
    suc (fp ℱ ⟨ a ⟩) + ℱ ⟨ _ ⟩                ≈⟨ +a-cong≈ (s≈s fp-fix) ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + 1 + ℱ ⟨ _ ⟩            ≈˘⟨ ≡→≈ +-assoc ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + (1 + ℱ ⟨ _ ⟩)          ≈⟨ a+-cong≈ (1+l-absorb $ fixbl-isLim $ nz-intro p) ⟩
    ℱ ⟨ fp ℱ ⟨ a ⟩ ⟩ + ℱ ⟨ _ ⟩                ≈⟨ fixbl-absorb (<→≺ q) ⟩
    ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩                ∎ where
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
  fp-suc-[n] {a} {n = suc n} =                begin-equality
    fp ℱ ⟨ suc a ⟩ [ suc n ]                  ≈⟨ fp-suc-[s] ⟩
    ℱ ⟨ fp ℱ ⟨ suc a ⟩ [ n ] ⟩                ≈⟨ fixbl-cong≈ fp-suc-[n] ⟩
    ℱ ⟨ Itₙ (ℱ ⟨_⟩) (suc (fp ℱ ⟨ a ⟩)) n ⟩    ∎ where open CrossTreeReasoning
```

### 性质的封闭

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
    q {n = suc n} = +-pres≼ (s≼s (fp-pres≼ p)) (fixbl-pres≼ q)
```

```agda
  fp-cong≈ : a ≈ b → fp ℱ ⟨ a ⟩ ≈ fp ℱ ⟨ b ⟩
  fp-cong≈ (p , q) = fp-pres≼ p , fp-pres≼ q
```

```agda
  fp-isLim : NonZero a → isLim (fp ℱ ⟨ a ⟩)
  fp-isLim {(zero)} _ = _
  fp-isLim {suc a} _  = _
  fp-isLim {lim f} _  = _
```

```agda
  fp-absorb : a ≺ b → fp ℱ ⟨ a ⟩ + fp ℱ ⟨ b ⟩ ≈ fp ℱ ⟨ b ⟩
  fp-absorb {a} {b = suc b} (s≼s a≼b) =
    (l≼ λ {n} →                               begin
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]       ≤⟨ +a-pres≼ (fp-pres≼ a≼b) ⟩
      fp ℱ ⟨ b ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]       ≤⟨ +a-pres≼ ≼-zero ⟩
      suc (fp ℱ ⟨ b ⟩) + fp ℱ ⟨ suc b ⟩ [ n ] ≤⟨ a+-pres≼ fixbl-infl≼ ⟩
      suc (fp ℱ ⟨ b ⟩) + ℱ ⟨ _ ⟩              ≈⟨ ≈-refl ⟩
      fp ℱ ⟨ suc b ⟩ [ suc n ]                ≤⟨ f≼l {n = suc n} ⟩
      fp ℱ ⟨ suc b ⟩                          ∎) ,
    (l≼ λ {n} →                               begin
      fp ℱ ⟨ suc b ⟩ [ n ]                    ≤⟨ a+-infl≼ ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ n ]       <⟨ a+-pres≺ (<→≺ (Fixpoints.wₛ ℱ)) ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩ [ suc n ]   ≤⟨ f≼l {n = suc n} ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ suc b ⟩             ∎) where
    open CrossTreeReasoning
  fp-absorb {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
    open CrossTreeReasoning
    aux : fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f m ⟩ ≼ lim- (λ m → fp ℱ ⟨ f m ⟩)
    aux {m} with <-cmp n m
    ... | tri< n<m _ _ = ≼l $                 begin
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f m ⟩               ≤⟨ fst (fp-absorb a≺fm) ⟩
      fp ℱ ⟨ f m ⟩                            ∎ where
      a≺fm =                                  begin-strict
        a                                     <⟨ a≺fn ⟩
        f n                                   <⟨ <→≺ (seq-pres n<m) ⟩
        f m                                   ∎
    ... | tri≈ _ refl _ = ≼l $                begin
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f n ⟩               ≤⟨ fst (fp-absorb a≺fn) ⟩
      fp ℱ ⟨ f n ⟩                            ∎
    ... | tri> _ _ m<n = ≼l $                 begin
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f m ⟩               ≤⟨ a+-pres≼ (fp-pres≼ fm≼fn) ⟩
      fp ℱ ⟨ a ⟩ + fp ℱ ⟨ f n ⟩               ≤⟨ fst (fp-absorb a≺fn) ⟩
      fp ℱ ⟨ f n ⟩                            ∎ where
      fm≼fn =                                 begin
        f m                                   <⟨ <→≺ (seq-pres m<n) ⟩
        f n                                   ∎
```

```agda
fp-fixbl : ∀ {ℱ} → Fixable ℱ → Fixable (fp ℱ)
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

η-lim : ⦃ _ : isLim a ⦄ → η ⟨ a ⟩ ≡ lim (λ n → η ⟨ a [ n ] ⟩) ⦃ nml-pres η []-wf ⦄
η-lim {lim f} = refl
```

```agda
η-fix : η ⟨ a ⟩ ≈ ζ ⟨ η ⟨ a ⟩ ⟩
η-fix = Fixable.fp-fix ζ-fixbl

η-suc-[n] : η ⟨ suc a ⟩ [ n ] ≈ Itₙ (ζ ⟨_⟩) (suc (η ⟨ a ⟩)) n
η-suc-[n] = Fixable.fp-suc-[n] ζ-fixbl
```
