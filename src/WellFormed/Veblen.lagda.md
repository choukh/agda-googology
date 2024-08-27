---
title: 形式化大数数学 (2.5 - 超限元Veblen函数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.5 - 超限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Veblen.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Veblen.lagda.md)  
> 高亮渲染: [Veblen.html](https://choukh.github.io/agda-googology/WellFormed.Veblen.html)  

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module WellFormed.Veblen where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
open import WellFormed.CrossTree
open import WellFormed.Fixpoints

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
```

```agda
record Jumper : Type where
  constructor by
  field
    jump-init : Ord
    jump-step : ℕ → Func
    ⦃ jump-init-nz ⦄ : NonZero jump-init
    ⦃ jump-step-nz ⦄ : NonZero (jump-step n b)
    jump-step-infl≼ : (jump-step n) inflates _≼_
    jump-step-pres≼ : (jump-step n) preserves _≼_
```

```agda
  F⁺ : Func
  F⁺-pres-rd : F⁺ preserves Road
  F⁺-pres : F⁺ preserves _<_
  F⁺-pres = map F⁺-pres-rd
```

```agda
  F⁺ zero    = jump-init
  F⁺ (suc a) = let b = suc (F⁺ a) in
               b + lim (Itₙ (λ n x → x + jump-step n b) 0) ⦃ +-infl ⦄
  F⁺ (lim f) = lim (F⁺ ∘ f) ⦃ F⁺-pres it ⦄
```

```agda
  F⁺-pres-rd zero         = rd[ 0 ] $ zero
  F⁺-pres-rd (suc r)      = rd[ 0 ] $ suc $ F⁺-pres-rd r
  F⁺-pres-rd (lim {n} r)  = rd[ n ] $ F⁺-pres-rd r
```

```agda
  F⁺-infl≼ : F⁺ inflates _≼_
  F⁺-infl≼ {(zero)} = z≼
  F⁺-infl≼ {suc x} = ≼[ 0 ] (s≼s F⁺-infl≼)
  F⁺-infl≼ {lim f} = l≼l F⁺-infl≼
```

```agda
  F⁺-isLim : ⦃ NonZero a ⦄ → isLim (F⁺ a)
  F⁺-isLim {suc a} = _
  F⁺-isLim {lim f} = _
```

```agda
  F⁺-pres≼ : F⁺ preserves _≼_
  F⁺-pres≼ {y = zero} z≼ = ≼-refl
  F⁺-pres≼ {y = suc y} z≼ = ≼[ 0 ] (≼-suc (F⁺-pres≼ z≼))
  F⁺-pres≼ {y = lim f} z≼ = ≼[ 0 ] (F⁺-pres≼ z≼)
  F⁺-pres≼ (≼l p) = ≼l (F⁺-pres≼ p)
  F⁺-pres≼ (l≼ p) = l≼ (F⁺-pres≼ p)
  F⁺-pres≼ (s≼s {a} {b} p) = l≼l (+-pres≼ (s≼s (F⁺-pres≼ p)) q) where
    q : Itₙ (λ n x → x + jump-step n (suc (F⁺ a))) 0 n
      ≼ Itₙ (λ n x → x + jump-step n (suc (F⁺ b))) 0 n
    q {(zero)} = ≼-refl
    q {suc n} = +-pres≼ q $ jump-step-pres≼ $ s≼s $ F⁺-pres≼ p
```

```agda
  F⁺[n]≼ : F⁺ (suc a) [ n ] ≼ Itₙ (λ n x → x + jump-step n (suc (F⁺ a))) 0 (suc n)
  F⁺[n]≼ {n = zero} = {!   !}
  F⁺[n]≼ {n = suc n} = {!   !}
```

```agda
  F⁺-absorb-n : F⁺ a + F⁺ (suc a) [ n ] ≼ F⁺ (suc a) [ suc n ]
  F⁺-absorb-n = +-pres≼ ≼-zero F⁺[n]≼
```

```agda
  jump_ : FNormal
  jump_ = normal F⁺ F⁺-pres ≈-refl , fixable F⁺-infl≼ F⁺-pres≼ ⦃ F⁺-isLim ⦄ F⁺-absorb-n
```
