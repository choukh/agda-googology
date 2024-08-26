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
Itₙ : (ℕ → Func) → Ord → Seq
Itₙ F i zero = i
Itₙ F i (suc n) = F n (Itₙ F i n)
```

```agda
record Normal : Type where
  constructor normal
  field func : Func
  private F = func
  field
    nml-pres : F preserves _<_
    continuous : ∀ {f} {w : wf f} → F (lim f ⦃ w ⦄) ≈ lim (F ∘ f) ⦃ nml-pres w ⦄
    ⦃ nml-zero-nz ⦄ : NonZero (F 0)

  instance
    nml-nz : NonZero (F a)
    nml-nz {(zero)} = it
    nml-nz {suc a} = nz-intro $ begin-strict
      0                         ≤⟨ z≤ ⟩
      F _                       <⟨ nml-pres zero₁ ⟩
      F (suc _)                 ∎ where open SubTreeReasoning
    nml-nz {lim f} = nz-intro $ begin-strict
      0                         <⟨ nz-elim ⟩
      F (f 0)                   <⟨ nml-pres f<l ⟩
      F (lim _)                 ∎ where open SubTreeReasoning

    lfp-wf : wf (Itₙ (λ _ → F) 0)
    lfp-wf {(zero)} = nz-elim
    lfp-wf {suc n} = nml-pres lfp-wf

  lfp : Ord
  lfp = lim (Itₙ (λ _ → F) 0)

  lfp-fix : lfp ≈ F lfp
  lfp-fix =                     begin-equality
    lfp                         ≈⟨ l≈ls ⟩
    lim- (F ∘ Itₙ (λ _ → F) 0)  ≈˘⟨ continuous ⟩
    F lfp                       ∎ where open CrossTreeReasoning
```

```agda
module Jump
  (Z : Ord)
  (⦃ Z-nz ⦄ : NonZero Z)
  (S : Ord → ℕ → Func)
  (S-wf : ∀ {a} → wf (Itₙ (S (suc a)) (suc a)))
  where

  F⁺ : Func
  F⁺-pres-rd : F⁺ preserves Road
  F⁺-pres : F⁺ preserves _<_
  F⁺-pres = map F⁺-pres-rd

  F⁺ zero    = Z
  F⁺ (suc a) = let j = suc (F⁺ a) in
               lim (Itₙ (S j) j) ⦃ S-wf ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄

  F⁺-pres-rd zero         = rd[ 0 ] $ zero
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ suc $ F⁺-pres-rd r
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r

  jump : Normal
  jump = normal F⁺ F⁺-pres ≈-refl

open Jump public using (jump)
```

## 不动点的枚举

```agda
module FpEnum (ν : Normal) where
  open Normal ν renaming (func to F)

  S : Ord → ℕ → Func
  S j _ x = j + F x

  S-wf : wf (Itₙ (S a) a)
  S-wf {n = zero} = +-infl
  S-wf {n = suc n} = +-pres (nml-pres S-wf)

  fpⁿ : Normal
  fpⁿ = jump lfp S S-wf

  F′ : Func
  F′ = Normal.func fpⁿ

  F′-0 : F′ 0 ≡ lfp
  F′-0 = refl

  F′-suc : F′ (suc a) ≡ lim (Itₙ (λ _ x → suc (F′ a) + F x) (suc (F′ a))) ⦃ S-wf ⦄
  F′-suc = refl

  F′-lim : {w : wf f} → F′ (lim f ⦃ w ⦄) ≡ lim- (λ n → F′ (f n))
  F′-lim = refl

open FpEnum public using (fpⁿ)
```

### 跨树性质

```agda
≼a : ⦃ _ : isLim a ⦄ → b ≼ a [ n ] → b ≼ a
≼a {lim f} = ≼l

a≼ : ⦃ _ : isLim a ⦄ → (∀ {n} → a [ n ] ≼ b) → a ≼ b
a≼ {lim f} = l≼

[]≼a : ⦃ _ : isLim a ⦄ → a [ n ] ≼ a
[]≼a {lim f} = f≼l
```

```agda
+l-isLim : ⦃ _ : isLim b ⦄ → isLim (a + b)
+l-isLim {lim f} = tt

a+[] : ⦃ l : isLim b ⦄ → let instance _ = +l-isLim ⦃ l ⦄ in
  a + b [ n ] ≡ (a + b) [ n ]
a+[] {lim f} = refl
```

```agda
record Fixable (ν : Normal) : Type where
  constructor fixable
  open Normal ν       renaming (func to F)
  open Normal (fpⁿ ν) renaming (func to F′) using ()
  field
    fixbl-infl≼ : F inflates _≼_
    fixbl-pres≼ : F preserves _≼_
    fixbl-isLim : ∀ {a} → ⦃ NonZero a ⦄ → isLim (F a)
    fixbl-wf    : let instance _ = fixbl-isLim in
                  ∀ {a} → wf λ n → F (suc a) [ n ]
    fixbl-wf-+  : let instance _ = fixbl-isLim in
                  ∀ {a} → F a + F (suc a) [ n ] ≼ F (suc a) [ suc n ]

  fixbl-cong≈ : a ≈ b → F a ≈ F b
  fixbl-cong≈ (p , q) = fixbl-pres≼ p , fixbl-pres≼ q
```

```agda
  fixbl-absorb : a ≺ b → F a + F b ≈ F b
  fixbl-absorb {a} {b = suc b} (s≼s a≼b) =
    (a≼ λ {n} →                           begin
      (F a + F (suc b)) [ n ]             ≈˘⟨ ≡→≈ a+[] ⟩
      F a + F (suc b) [ n ]               ≤⟨ +a-pres≼ (fixbl-pres≼ a≼b) ⟩
      F b + F (suc b) [ n ]               ≤⟨ fixbl-wf-+ ⟩
      F (suc b) [ suc n ]                 ≤⟨ []≼a ⟩
      F (suc b)                           ∎) ,
    (a≼ λ {n} →                           begin
      F (suc b) [ n ]                     ≤⟨ a+-infl≼ ⟩
      F a + F (suc b) [ n ]               <⟨ a+-pres≺ (<→≺ fixbl-wf) ⟩
      F a + F (suc b) [ suc n ]           ≤⟨ a+-pres≼ []≼a ⟩
      F a + F (suc b)                     ∎) where
    open CrossTreeReasoning
    instance
      _ = fixbl-isLim
      _ : isLim (F a + F (suc b))
      _ = +l-isLim
      _ : isLim (F b + F (suc b))
      _ = +l-isLim
  fixbl-absorb {a} {b = lim f} (≼l {n} a≺fn) =
    (                                     begin
      F a + F (lim f)                     ≈⟨ a+-cong≈ continuous ⟩
      F a + lim- (λ n → F (f n))          ≤⟨ l≼ aux ⟩
      lim- (λ n → F (f n))                ≈˘⟨ continuous ⟩
      F (lim f)                           ∎) ,
    (                                     begin
      F (lim f)                           ≈⟨ continuous ⟩
      lim- (λ n → F (f n))                ≤⟨ l≼l a+-infl≼ ⟩
      F a + lim- (λ n → F (f n))          ≈˘⟨ a+-cong≈ continuous ⟩
      F a + F (lim f)                     ∎) where
    open CrossTreeReasoning
    aux : F a + F (f m) ≼ lim- λ m → F (f m)
    aux {m} with <-cmp n m
    ... | tri< n<m _ _ = ≼l $             begin
      F a + F (f m)                       ≤⟨ fst (fixbl-absorb a≺fm) ⟩
      F (f m)                             ∎ where
      a≺fm =                              begin-strict
        a                                 <⟨ a≺fn ⟩
        f n                               <⟨ <→≺ (seq-pres n<m) ⟩
        f m                               ∎
    ... | tri≈ _ refl _ = ≼l $            begin
      F a + F (f n)                       ≤⟨ fst (fixbl-absorb a≺fn) ⟩
      F (f n)                             ∎
    ... | tri> _ _ m<n = ≼l $             begin
      F a + F (f m)                       ≤⟨ a+-pres≼ (fixbl-pres≼ fm≼fn) ⟩
      F a + F (f n)                       ≤⟨ fst (fixbl-absorb a≺fn) ⟩
      F (f n)                             ∎ where
      fm≼fn =                             begin
        f m                               <⟨ <→≺ (seq-pres m<n) ⟩
        f n                               ∎
```

```agda
  F′-fix : F′ a ≈ F (F′ a)
  F′-suc-[n] : F′ (suc a) [ n ] ≈ Itₙ (λ _ → F) (suc (F′ a)) n
```

```agda
  F′-fix {a = zero}  = lfp-fix
  F′-fix {a = suc a} = p , q where
    open CrossTreeReasoning
    p =                                   begin
      F′ (suc a)                          ≤⟨ l≼l fixbl-infl≼ ⟩
      lim- (λ n → F _)                    ≈˘⟨ continuous ⟩
      F (F′ (suc a))                      ∎
    q[n] = λ {n} →                        begin
      F (F′ (suc a) [ n ])                ≈⟨ fixbl-cong≈ F′-suc-[n] ⟩
      F (Itₙ (λ _ → F) (suc (F′ a)) n)    ≈⟨ ≈-refl ⟩
      Itₙ (λ _ → F) (suc (F′ a)) (suc n)  ≈˘⟨ F′-suc-[n] ⟩
      F′ (suc a) [ suc n ]                ∎
    q =                                   begin
      F (F′ (suc a ))                     ≈⟨ continuous ⟩
      lim- (λ n → F _)                    ≤⟨ l≼ls q[n] ⟩
      F′ (suc a)                          ∎
  F′-fix {a = lim f} =                    begin-equality
    F′ (lim f)                            ≈⟨ l≈l F′-fix ⟩
    lim- (λ n → F _)                      ≈˘⟨ continuous ⟩
    F (F′ (lim f))                        ∎ where open CrossTreeReasoning
```

```agda
  F′-suc-[0] : F′ (suc a) [ 0 ] ≡ suc (F′ a)
  F′-suc-[0] = refl
```

```agda
  F′-suc-[s] : F′ (suc a) [ suc n ] ≈ F (F′ (suc a) [ n ])
  F′-suc-[s] {a} {n} =                    begin-equality
    F′ (suc a) [ suc n ]                  ≈⟨ ≈-refl ⟩
    suc (F′ a) + F _                      ≈⟨ +a-cong≈ (s≈s F′-fix) ⟩
    F (F′ a) + 1 + F _                    ≈˘⟨ ≡→≈ +-assoc ⟩
    F (F′ a) + (1 + F _)                  ≈⟨ a+-cong≈ $ 1+l-absorb $ fixbl-isLim ⦃ nz-intro p ⦄ ⟩
    F (F′ a) + F _                        ≈⟨ fixbl-absorb (<→≺ q) ⟩
    F (F′ (suc a) [ n ])                  ∎ where
    open CrossTreeReasoning
    p : 0 < F′ (suc a) [ m ]
    p {(zero)} = z<s
    p {suc m} = <-trans z<s (+-infl ⦃ nml-nz ⦄)
    q : F′ a < F′ (suc a) [ m ]
    q {(zero)} = zero₁
    q {suc m} = <-trans q (FpEnum.S-wf ν)
```

```agda
  F′-suc-[n] {n = zero} = ≡→≈ F′-suc-[0]
  F′-suc-[n] {a} {n = suc n} =            begin-equality
    F′ (suc a) [ suc n ]                  ≈⟨ F′-suc-[s] ⟩
    F (F′ (suc a) [ n ])                  ≈⟨ fixbl-cong≈ F′-suc-[n] ⟩
    F (Itₙ (λ _ → F) (suc (F′ a)) n)      ∎ where open CrossTreeReasoning
```

### 性质的封闭

```agda
  F′-infl≼ : F′ inflates _≼_
  F′-infl≼ {(zero)} = z≼
  F′-infl≼ {suc _}  = ≼l {n = 0} (s≼s F′-infl≼)
  F′-infl≼ {lim f}  = l≼l F′-infl≼
```

```agda
  F′-pres≼ : F′ preserves _≼_
  F′-pres≼ {y = zero}  z≼ = ≼-refl
  F′-pres≼ {y = suc y} z≼ = ≼l {n = 0} (≼-suc (F′-pres≼ z≼))
  F′-pres≼ {y = lim f} z≼ = ≼l {n = 0} (F′-pres≼ z≼)
  F′-pres≼ (≼l {n} p)     = ≼l {n = n} (F′-pres≼ p)
  F′-pres≼ (l≼ p)         = l≼ (F′-pres≼ p)
  F′-pres≼ (s≼s {a} {b} p) = l≼l q where
    q : F′ (suc a) [ n ] ≼ F′ (suc b) [ n ]
    q {n = zero} = s≼s (F′-pres≼ p)
    q {n = suc n} = +-pres≼ (s≼s (F′-pres≼ p)) (fixbl-pres≼ q)
```

```agda
  F′-cong≈ : a ≈ b → F′ a ≈ F′ b
  F′-cong≈ (p , q) = F′-pres≼ p , F′-pres≼ q
```

```agda
  F′-isLim : ⦃ NonZero a ⦄ → isLim (F′ a)
  F′-isLim {(zero)} = _
  F′-isLim {suc a}  = _
  F′-isLim {lim f}  = _
```

```agda
  F′-absorb : a ≺ b → F′ a + F′ b ≈ F′ b
  F′-absorb {a} {b = suc b} (s≼s a≼b) =
    (l≼ λ {n} →                           begin
      F′ a + F′ (suc b) [ n ]             ≤⟨ +a-pres≼ (F′-pres≼ a≼b) ⟩
      F′ b + F′ (suc b) [ n ]             ≤⟨ +a-pres≼ ≼-zero ⟩
      suc (F′ b) + F′ (suc b) [ n ]       ≤⟨ a+-pres≼ fixbl-infl≼ ⟩
      suc (F′ b) + F _                    ≈⟨ ≈-refl ⟩
      F′ (suc b) [ suc n ]                ≤⟨ f≼l {n = suc n} ⟩
      F′ (suc b)                          ∎) ,
    (l≼ λ {n} →                           begin
      F′ (suc b) [ n ]                    ≤⟨ a+-infl≼ ⟩
      F′ a + F′ (suc b) [ n ]             <⟨ a+-pres≺ (<→≺ (FpEnum.S-wf ν)) ⟩
      F′ a + F′ (suc b) [ suc n ]         ≤⟨ f≼l {n = suc n} ⟩
      F′ a + F′ (suc b)                   ∎) where
    open CrossTreeReasoning
  F′-absorb {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
    open CrossTreeReasoning
    aux : F′ a + F′ (f m) ≼ lim- (λ m → F′ (f m))
    aux {m} with <-cmp n m
    ... | tri< n<m _ _ = ≼l $             begin
      F′ a + F′ (f m)                     ≤⟨ fst (F′-absorb a≺fm) ⟩
      F′ (f m)                            ∎ where
      a≺fm =                              begin-strict
        a                                 <⟨ a≺fn ⟩
        f n                               <⟨ <→≺ (seq-pres n<m) ⟩
        f m                               ∎
    ... | tri≈ _ refl _ = ≼l $            begin
      F′ a + F′ (f n)                     ≤⟨ fst (F′-absorb a≺fn) ⟩
      F′ (f n)                            ∎
    ... | tri> _ _ m<n = ≼l $             begin
      F′ a + F′ (f m)                     ≤⟨ a+-pres≼ (F′-pres≼ fm≼fn) ⟩
      F′ a + F′ (f n)                     ≤⟨ fst (F′-absorb a≺fn) ⟩
      F′ (f n)                            ∎ where
      fm≼fn =                             begin
        f m                               <⟨ <→≺ (seq-pres m<n) ⟩
        f n                               ∎
```

```agda
fpᶠ : ∀ {ν} → Fixable ν → Fixable (fpⁿ ν)
fpᶠ p = fixable F′-infl≼ F′-pres≼ F′-isLim {!   !} {!   !} --F′-absorb
  where open Fixable p
```

```agda
open Normal public
FNormal = Σ Normal Fixable

fp : FNormal → FNormal
fp (ν , p) = fpⁿ ν , fpᶠ p

_⟨_⟩ : FNormal → Func
(ν , _) ⟨ a ⟩ = func ν a

fixbl : ((ν , _) : FNormal) → Fixable ν
fixbl (ν , p) = p
```

## 不动点的实例

```agda
ω^-isLim : ⦃ NonZero a ⦄ → isLim (ω ^ a)
ω^-isLim {suc a} = _
ω^-isLim {lim f} = _
```

```
ω^ : FNormal
ω^ = normal (ω ^_) ^-pres ≈-refl
   , fixable a^-infl≼ a^-pres≼ ω^-isLim {!   !} {!   !} --ω^-absorb
```

```agda
ε ζ η : FNormal
ε = fp ω^
ζ = fp ε
η = fp ζ
```

```agda
η-0 : η ⟨ 0 ⟩ ≡ lim- (Itₙ (λ _ → ζ ⟨_⟩) 0)
η-0 = refl

η-suc : η ⟨ suc a ⟩ ≡ lim- (Itₙ (λ _ x → suc (η ⟨ a ⟩) + ζ ⟨ x ⟩) (suc (η ⟨ a ⟩)))
η-suc = refl

η-lim : ⦃ _ : wf f ⦄ → η ⟨ lim f ⟩ ≡ lim- λ n → η ⟨ f n ⟩
η-lim = refl
```

```agda
η-fix : η ⟨ a ⟩ ≈ ζ ⟨ η ⟨ a ⟩ ⟩
η-fix = Fixable.F′-fix (fixbl ζ)

η-suc-[n] : η ⟨ suc a ⟩ [ n ] ≈ Itₙ (λ _ → ζ ⟨_⟩) (suc (η ⟨ a ⟩)) n
η-suc-[n] = Fixable.F′-suc-[n] (fixbl ζ)
```
