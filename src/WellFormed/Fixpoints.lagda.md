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
    pres : F preserves _<_
    continuous : ∀ {f} {w : wf f} → F (lim f ⦃ w ⦄) ≈ lim (F ∘ f) ⦃ pres w ⦄
    ⦃ zero-nz ⦄ : NonZero (F 0)

  instance
    nz : NonZero (F a)
    nz {(zero)} = it
    nz {suc a} = nz-intro $ begin-strict
      0                         ≤⟨ z≤ ⟩
      F _                       <⟨ pres zero₁ ⟩
      F (suc _)                 ∎ where open SubTreeReasoning
    nz {lim f} = nz-intro $ begin-strict
      0                         <⟨ nz-elim ⟩
      F (f 0)                   <⟨ pres f<l ⟩
      F (lim _)                 ∎ where open SubTreeReasoning

    lfp-wf : wf (Itₙ (λ _ → F) 0)
    lfp-wf {(zero)} = nz-elim
    lfp-wf {suc n} = pres lfp-wf

  lfp : Ord
  lfp = lim (Itₙ (λ _ → F) 0)

  lfp-fix : lfp ≈ F lfp
  lfp-fix =                     begin-equality
    lfp                         ≈⟨ l≈ls ⟩
    lim- (F ∘ Itₙ (λ _ → F) 0)  ≈˘⟨ continuous ⟩
    F lfp                       ∎ where open CrossTreeReasoning
```

## 不动点的枚举

```agda
module FpEnum (ν : Normal) where
  open Normal ν renaming (func to F)

  w : wf (Itₙ (λ _ x → b + F x) b)
  w {n = zero} = +-infl
  w {n = suc n} = +-pres (pres w)

  F′ : Func
  F′-pres-rd : F′ preserves Road
  F′-pres : F′ preserves _<_
  F′-pres = map F′-pres-rd

  F′ zero = lfp
  F′ (suc a) = let b = suc (F′ a) in
               lim (Itₙ (λ _ x → b + F x) b) ⦃ w ⦄
  F′ (lim f) = lim (F′ ∘ f) ⦃ F′-pres it ⦄

  F′-pres-rd zero         = rd[ 0 ] $ zero
  F′-pres-rd (suc r)      = rd[ 0 ] $ suc $ F′-pres-rd r
  F′-pres-rd (lim {n} r)  = rd[ n ] $ F′-pres-rd r

  F′-0 : F′ 0 ≡ lfp
  F′-0 = refl

  F′-suc : F′ (suc a) ≡ lim (Itₙ (λ _ x → suc (F′ a) + F x) (suc (F′ a))) ⦃ w ⦄
  F′-suc = refl

  F′-lim : {w : wf f} → F′ (lim f ⦃ w ⦄) ≡ lim- (λ n → F′ (f n))
  F′-lim = refl

  fpⁿ : Normal
  fpⁿ = normal F′ F′-pres ≈-refl

open FpEnum public using (fpⁿ)
```

### 跨树性质

```agda
record Fixable (ν : Normal) : Type where
  constructor fixable
  open Normal ν       renaming (func to F)
  open Normal (fpⁿ ν) renaming (func to F′) using ()
  field
    infl≼ : F inflates _≼_
    pres≼ : F preserves _≼_
    ⦃ isL ⦄ : ∀ {a} → ⦃ NonZero a ⦄ → isLim (F a)
    absorb-n : ∀ {a} → F a + F (suc a) [ n ] ≼ F (suc a) [ suc n ]

  cong≈ : a ≈ b → F a ≈ F b
  cong≈ (p , q) = pres≼ p , pres≼ q
```

```agda
  +l-isLim : ⦃ _ : isLim b ⦄ → isLim (a + b)
  +l-isLim {lim f} = tt

  a+[] : ⦃ l : isLim b ⦄ → let instance _ = +l-isLim ⦃ l ⦄ in
    a + b [ n ] ≡ (a + b) [ n ]
  a+[] {lim f} = refl
```

```agda
  absorb : a ≺ b → F a + F b ≈ F b
  absorb {a} {b = suc b} (s≼s a≼b) =
    (a≼ λ {n} →                           begin
      (F a + F (suc b)) [ n ]             ≈˘⟨ ≡→≈ a+[] ⟩
      F a + F (suc b) [ n ]               ≤⟨ +a-pres≼ (pres≼ a≼b) ⟩
      F b + F (suc b) [ n ]               ≤⟨ absorb-n ⟩
      F (suc b) [ suc n ]                 ≤⟨ []≼a ⟩
      F (suc b)                           ∎) ,
    (a≼ λ {n} →                           begin
      F (suc b) [ n ]                     ≤⟨ a+-infl≼ ⟩
      F a + F (suc b) [ n ]               <⟨ a+-pres≺ (<→≺ []-wf) ⟩
      F a + F (suc b) [ suc n ]           ≤⟨ a+-pres≼ []≼a ⟩
      F a + F (suc b)                     ∎) where
    open CrossTreeReasoning
    instance
      _ : isLim (F a + F (suc b))
      _ = +l-isLim
      _ : isLim (F b + F (suc b))
      _ = +l-isLim
  absorb {a} {b = lim f} (≼l {n} a≺fn) =
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
      F a + F (f m)                       ≤⟨ fst (absorb a≺fm) ⟩
      F (f m)                             ∎ where
      a≺fm =                              begin-strict
        a                                 <⟨ a≺fn ⟩
        f n                               <⟨ <→≺ (seq-pres n<m) ⟩
        f m                               ∎
    ... | tri≈ _ refl _ = ≼l $            begin
      F a + F (f n)                       ≤⟨ fst (absorb a≺fn) ⟩
      F (f n)                             ∎
    ... | tri> _ _ m<n = ≼l $             begin
      F a + F (f m)                       ≤⟨ a+-pres≼ (pres≼ fm≼fn) ⟩
      F a + F (f n)                       ≤⟨ fst (absorb a≺fn) ⟩
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
      F′ (suc a)                          ≤⟨ l≼l infl≼ ⟩
      lim- (λ n → F _)                    ≈˘⟨ continuous ⟩
      F (F′ (suc a))                      ∎
    q[n] = λ {n} →                        begin
      F (F′ (suc a) [ n ])                ≈⟨ cong≈ F′-suc-[n] ⟩
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
    F (F′ a) + (1 + F _)                  ≈⟨ a+-cong≈ $ 1+l-absorb $ isL ⦃ nz-intro p ⦄ ⟩
    F (F′ a) + F _                        ≈⟨ absorb (<→≺ q) ⟩
    F (F′ (suc a) [ n ])                  ∎ where
    open CrossTreeReasoning
    p : 0 < F′ (suc a) [ m ]
    p {(zero)} = z<s
    p {suc m} = <-trans z<s (+-infl ⦃ nz ⦄)
    q : F′ a < F′ (suc a) [ m ]
    q {(zero)} = zero₁
    q {suc m} = <-trans q (FpEnum.w ν)
```

```agda
  F′-suc-[n] {n = zero} = ≡→≈ F′-suc-[0]
  F′-suc-[n] {a} {n = suc n} =            begin-equality
    F′ (suc a) [ suc n ]                  ≈⟨ F′-suc-[s] ⟩
    F (F′ (suc a) [ n ])                  ≈⟨ cong≈ F′-suc-[n] ⟩
    F (Itₙ (λ _ → F) (suc (F′ a)) n)      ∎ where open CrossTreeReasoning
```

### 性质的封闭

```agda
  F′-infl≼ : F′ inflates _≼_
  F′-infl≼ {(zero)} = z≼
  F′-infl≼ {suc _}  = ≼[ 0 ] (s≼s F′-infl≼)
  F′-infl≼ {lim f}  = l≼l F′-infl≼
```

```agda
  F′-pres≼ : F′ preserves _≼_
  F′-pres≼ {y = zero}  z≼ = ≼-refl
  F′-pres≼ {y = suc y} z≼ = ≼[ 0 ] (≼-suc (F′-pres≼ z≼))
  F′-pres≼ {y = lim f} z≼ = ≼[ 0 ] (F′-pres≼ z≼)
  F′-pres≼ (≼l {n} p)     = ≼[ n ] (F′-pres≼ p)
  F′-pres≼ (l≼ p)         = l≼ (F′-pres≼ p)
  F′-pres≼ (s≼s {a} {b} p) = l≼l q where
    q : F′ (suc a) [ n ] ≼ F′ (suc b) [ n ]
    q {n = zero} = s≼s (F′-pres≼ p)
    q {n = suc n} = +-pres≼ (s≼s (F′-pres≼ p)) (pres≼ q)
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
  F′-absorb-n : F′ a + F′ (suc a) [ n ] ≼ F′ (suc a) [ suc n ]
  F′-absorb-n {a} {n} =                 begin
    F′ a + F′ (suc a) [ n ]               ≤⟨ +a-pres≼ ≼-zero ⟩
    suc (F′ a) + F′ (suc a) [ n ]         ≤⟨ a+-pres≼ infl≼ ⟩
    suc (F′ a) + F (F′ (suc a) [ n ])     ≈⟨ ≈-refl ⟩
    F′ (suc a) [ suc n ]                  ∎ where open CrossTreeReasoning
```

```agda
fpᶠ : ∀ {ν} → Fixable ν → Fixable (fpⁿ ν)
fpᶠ p = fixable F′-infl≼ F′-pres≼ ⦃ F′-isLim ⦄ F′-absorb-n
  where open Fixable p
```

```agda
FNormal = Σ Normal Fixable

fp : FNormal → FNormal
fp (ν , p) = fpⁿ ν , fpᶠ p

_⟨_⟩ : FNormal → Func
(ν , _) ⟨ a ⟩ = Normal.func ν a

fixbl : ((ν , _) : FNormal) → Fixable ν
fixbl (ν , p) = p
```

## 不动点的实例

```agda
ω^-isLim : ⦃ NonZero a ⦄ → isLim (ω ^ a)
ω^-isLim {suc a} = _
ω^-isLim {lim f} = _
```

**引理 2-4-xx** 加法结合律的变体: $a + (a + ... + a) = (a + ... + a) + a$.  
**证明** 即证 $a + a ⋅ n = a ⋅ n + a$. 对 $n$ 归纳.

- 若 $n = 0$, 有 $a + 0 = 0 + a$.
- 若 $n = n'^+$, 有归纳假设 $a + a ⋅ n' = a ⋅ n' + a$, 于是有

$$
\begin{aligned}
a + a ⋅ n'^+ &= a + (a ⋅ n' + a) \\
&= (a + a ⋅ n') + a \\
&= (a ⋅ n' + a) + a \\
&= a ⋅ n'^+ + a \quad ∎
\end{aligned}
$$

注意这里的相等是内涵相等.

```agda
+-assoc-n : ⦃ _ : NonZero a ⦄ → a + a * fin n ≡ a * fin n + a
+-assoc-n {n = zero} = sym +a-id
+-assoc-n {a} {n = suc n} = begin-equality
  a + a * suc (fin n)     ≈⟨ refl ⟩
  a + (a * fin n + a)     ≈⟨ +-assoc ⟩
  a + a * fin n + a       ≈⟨ cong (_+ a) +-assoc-n ⟩
  a * suc (fin n) + a     ∎ where open SubTreeReasoning
```

```agda
ω^-absorb-n : ω ^ a + (ω ^ suc a) [ n ] ≼ (ω ^ suc a) [ suc n ]
ω^-absorb-n {a} {n} =                   begin
    ω ^ a + ω ^ a * fin n                 ≈⟨ ≡→≈ +-assoc-n ⟩
    ω ^ a * fin n + ω ^ a                 ≈⟨ ≈-refl ⟩
    ω ^ a * suc (fin n)                   ∎ where open CrossTreeReasoning; instance _ = ^-nz
```

```
ω^ : FNormal
ω^ = normal (ω ^_) ^-pres ≈-refl
   , fixable a^-infl≼ a^-pres≼ ⦃ ω^-isLim ⦄ ω^-absorb-n
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
