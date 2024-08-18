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
open import Lower using (_∘ⁿ_)
itn : Func → Ord → Seq
itn F i n = (F ∘ⁿ n) i
```

```agda
itω : (F : Func) (i : Ord) (w : wf (itn F i)) → Ord
itω F i w = lim (itn F i) ⦃ w ⦄
```

```agda
record Fixable : Type where
  constructor mkFixable
  field _⟨_⟩ : Func
  private F = _⟨_⟩
  field
    fix-pres : F preserves _<_
    ⦃ fix-nz ⦄ : NonZero (F 0)
  instance
    fix-suc-nz : NonZero (F (suc a))
    fix-suc-nz = nz-intro $ begin-strict
      0                     ≤⟨ z≤ ⟩
      F _                   <⟨ fix-pres zero₁ ⟩
      F (suc _)             ∎ where open SubTreeReasoning
```

```agda
module Fixpt (ℱ : Fixable) where
  open Fixable ℱ renaming (_⟨_⟩ to F)

  F′ : Func
  F′-pres-rd : F′ preserves Road
  F′-pres : F′ preserves _<_
  F′-pres = map F′-pres-rd
```

```agda
  F′ zero = itω F 0 w
    module Zero where
    w : wf (itn F 0)
    w {(zero)} = nz-elim
    w {suc n} = fix-pres w
  F′ (suc a) = itω (λ x → i + F x) i w
    module Suc where
    i = suc (F′ a)
    w : wf (itn (λ x → i + F x) i)
    w {n = zero} = +-infl
    w {n = suc n} = +-pres (fix-pres w)
  F′ (lim f) = lim (λ n → F′ (f n)) ⦃ F′-pres it ⦄
```

```agda
  F′-pres-rd {(x)} zero         = rd[ 0 ] zero
  F′-pres-rd {(x)} (suc r)      = rd[ 0 ] $ rd-trans (F′-pres-rd r) zero
  F′-pres-rd {(x)} (lim {n} r)  = rd[ n ] $ F′-pres-rd r
```

```agda
fixpt : Fixable → Fixable
fixpt ℱ = mkFixable F′ F′-pres ⦃ _ ⦄ where open Fixpt ℱ
```

```agda
base-ω : Fixable
base-ω = mkFixable (ω ^_) ^-pres
```

```agda
ε ζ η : Fixable
ε = fixpt base-ω
ζ = fixpt ε
η = fixpt ζ
```

```agda
open Fixable public

sε : Func
sε a = suc (ε ⟨ a ⟩)

εs : Func
εs a = ε ⟨ suc a ⟩
```

```agda
ε-0 : ε ⟨ 0 ⟩ ≡ itω (ω ^_) 0 _
ε-0 = refl

ε-suc : ε ⟨ suc a ⟩ ≡ itω (λ x → sε a + ω ^ x) (sε a) _
ε-suc = refl

ε-lim : {w : wf f} → ε ⟨ lim f ⦃ w ⦄ ⟩ ≡ lim- λ n → ε ⟨ f n ⟩
ε-lim = refl
```

```agda
ε-fix : ε ⟨ a ⟩ ≈ ω ^ ε ⟨ a ⟩
ε-suc-[n] : εs a [ n ] ≈ itn (ω ^_) (sε a) n
```

```agda
ε-fix {(zero)} = l≈ls z≼
ε-fix {suc a} = l≼l p , l≼ls (fst q) where
  p : εs a [ n ] ≼ ω ^ εs a [ n ]
  p = a^-infl≼
  q : ω ^ εs a [ n ] ≈ εs a [ suc n ]
  q {n} =                               begin-equality
    ω ^ εs a [ n ]                      ≈⟨ a^-cong≈ ε-suc-[n] ⟩
    ω ^ itn (ω ^_) (sε a) n             ≈⟨ ≈-refl ⟩
    itn (ω ^_) (sε a) (suc n)           ≈˘⟨ ε-suc-[n] ⟩
    εs a [ suc n ]                      ∎ where open CrossTreeReasoning
ε-fix {lim f} = l≈l ε-fix
```

```agda
ε-suc-[0] : εs a [ 0 ] ≡ sε a
ε-suc-[0] = refl
```

```agda
ε-suc-[s] : εs a [ suc n ] ≈ ω ^ εs a [ n ]
ε-suc-[s] {a} {n} =                     begin-equality
  εs a [ suc n ]                        ≈⟨ ≈-refl ⟩
  ε ⟨ a ⟩ + 1 + ω ^ εs a [ n ]          ≈⟨ +a-cong≈ $ s≈s ε-fix ⟩
  ω ^ ε ⟨ a ⟩ + ω ^ 0 + ω ^ εs a [ n ]  ≈⟨ ω^-absorb2 (<→≺ p) (<→≺ q) ⟩
  ω ^ εs a [ n ]                        ∎ where
  open CrossTreeReasoning
  p : ε ⟨ a ⟩ < εs a [ m ]
  p {(zero)} = zero₁
  p {suc m} = <-trans p (Fixpt.Suc.w _ _)
  q : 0 < εs a [ m ]
  q {(zero)} = z<s
  q {suc m} = <-trans z<s (+-infl ⦃ ^-nz ⦄)
```

```agda
ε-suc-[n] {n = zero} = ≡→≈ ε-suc-[0]
ε-suc-[n] {a} {n = suc n} =             begin-equality
  εs a [ suc n ]                        ≈⟨ ε-suc-[s] ⟩
  ω ^ εs a [ n ]                        ≈⟨ a^-cong≈ ε-suc-[n] ⟩
  ω ^ itn (ω ^_) (sε a) n               ∎ where open CrossTreeReasoning
```
