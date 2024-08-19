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
continuous : ∀ {F} → F preserves _<_ → Set
continuous {F} pres = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘ f) ⦃ pres it ⦄
```

```agda
open import Lower using (_∘ⁿ_)
Iₙ : Func → Ord → Seq
Iₙ F i n = (F ∘ⁿ n) i
```

```agda
record Normal : Type where
  constructor mkNormal
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
module Jump (i : Ord) (F : Func) ⦃ l : ∀ {a} → IsLim (F a) ⦄
  (Gₙ : Func → Ord → Seq) (w : wf (Gₙ F i))
  where

  jump : Func
  jump zero = lim (Gₙ F i) ⦃ w ⦄
  jump (suc a) = lim (Gₙ (λ x → j + F x) j) ⦃ {!   !} ⦄
    module Suc where
    j = suc (jump a)
  jump (lim f) = lim (jump ∘ f) ⦃ {!   !} ⦄
```
