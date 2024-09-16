---
title: 形式化大数数学 (3.0 - 高阶递归序数层级)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 高阶递归序数层级)

> 交流Q群: 893531731  
> 本文源码: [HigherOrd.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/OCF/HigherOrd.lagda.md)  
> 高亮渲染: [HigherOrd.html](httrsps://choukh.github.io/agda-googology/OCF.HigherOrd.html)  

## 工作环境

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module OCF.HigherOrd where
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
```

```agda
open import WellFormed.Base as Level public
  using (a; b; c; n; m; zero; suc; lim)
  renaming (Ord to Level; Road to _⊏_; _<_ to _⊏₁_;
    rd-trans to ⊏-trans; f<l-rd to f⊏l; rd-trich to ⊏-trich)

open Level.Foundations public
open Level.CanonicalRoad public using (cano; cano-2const)

import Cubical.Foundations.Prelude as 🧊
open import Cubical.Foundations.HLevels using (isProp→)
```

## 高阶递归序数层级

```agda
module _ (ℓ : Level) (El : ∀ a → a ⊏ ℓ → Type)
  (R : ∀ {a} {aℓ : a ⊏ ℓ} → El a aℓ → El a aℓ → Type) where

  data U : Type
  data Road : U → U → Type
```

```agda
  Road₁ : U → U → Type
  Road₁ α β = ∥ Road α β ∥₁
```

```agda
  private variable
    α β : U
    aℓ : a ⊏ ℓ
    ν : El a aℓ
```

```agda
  wf : (El a aℓ → U) → Type
  wf f = ∀ {ν μ} → R ν μ → Road₁ (f ν) (f μ)
```

```agda
  data U where
    zero : U
    suc : U → U
    lim : (aℓ : a ⊏ ℓ) (f : El a aℓ → U) (w : wf f) → U
```

```agda
  data Road where
    zero : Road α (suc α)
    suc  : Road α β → Road α (suc β)
    lim  : {f : El a aℓ → U} (w : wf f) → Road α (f ν) → Road α (lim aℓ f w)
```

## 层级的表示

```agda
variable
  ℓ ℓ′ : Level
  aℓ : a ⊏ ℓ
```

```agda
Elm : ∀ a → a ⊏ ℓ → Type
_<ᵉ_ : Elm a aℓ → Elm a aℓ → Type
```

```agda
Elm a zero = U a Elm _<ᵉ_
Elm a (suc aℓ) = Elm a aℓ
Elm a (lim aℓ) = Elm a aℓ
```

```agda
_<ᵉ_ {aℓ = zero} = Road _ Elm _<ᵉ_
_<ᵉ_ {aℓ = suc aℓ} = _<ᵉ_ {aℓ = aℓ}
_<ᵉ_ {aℓ = lim aℓ} = _<ᵉ_ {aℓ = aℓ}
```

```agda
Ord : Level → Type
Ord a = U a Elm _<ᵉ_
variable α β : Ord a

_<_ : Ord a → Ord a → Type
_<_ = Road _ Elm _<ᵉ_

_<₁_ : Ord a → Ord a → Type
_<₁_ = Road₁ _ Elm _<ᵉ_
```

```agda
Elm≡Ord : Elm a aℓ ≡ Ord a
Elm≡Ord {aℓ = zero} = refl
Elm≡Ord {aℓ = suc aℓ} = Elm≡Ord {aℓ = aℓ}
Elm≡Ord {aℓ = lim aℓ} = Elm≡Ord {aℓ = aℓ}
```

```agda
ord : Elm a aℓ → Ord a
ord α = subst id Elm≡Ord α

elm : Ord a → Elm a aℓ
elm α = subst id (sym Elm≡Ord) α
```

```agda
<ᵉ⥱< : {α̂ β̂ : Elm a aℓ} → α̂ <ᵉ β̂ ≡ ord α̂ < ord β̂
<ᵉ⥱< {aℓ = zero} = refl
<ᵉ⥱< {aℓ = suc aℓ} = <ᵉ⥱< {aℓ = aℓ}
<ᵉ⥱< {aℓ = lim aℓ} = <ᵉ⥱< {aℓ = aℓ}
```

```agda
<⥱<ᵉ : α < β ≡ elm {aℓ = aℓ} α <ᵉ elm β
<⥱<ᵉ {aℓ = zero} = refl
<⥱<ᵉ {aℓ = suc aℓ} = <⥱<ᵉ {aℓ = aℓ}
<⥱<ᵉ {aℓ = lim aℓ} = <⥱<ᵉ {aℓ = aℓ}
```
