---
title: 形式化大数数学 (3.0 -邱奇-克莱尼序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 邱奇-克莱尼序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/OCF/Base.lagda.md)  
> 高亮渲染: [Base.html](httrsps://choukh.github.io/agda-googology/OCF.Base.html)  

## 工作环境

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module OCF.Base where
```

**Cubical库**

```agda
open import Cubical.Foundations.Prelude public
  hiding (Level; Lift; lift; lower) renaming (_∎ to _≡∎)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Transport public
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
open import Cubical.HITs.PropositionalTruncation public
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; _∷_; lookup) renaming (map to map⃗)
open import Function public using (id; _∘_; _$_; _∋_; _⟨_⟩_; case_of_)
open import Relation.Binary.Definitions public
open import Relation.Binary.PropositionalEquality as Eq public
  using () renaming (_≡_ to _＝_; refl to rfl)
open import Induction.WellFounded as WF public
```

**桥接库**

用于处理Cubical库与标准库混用时的一些问题.

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Unit public using (⊤; tt; isProp⊤)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

## 抽象树序数

**定义** 序结构

```agda
OrderStruct : Type₁
OrderStruct = Σ Type λ A → A → A → Type
```

**定义** 由序结构索引的序结构族前段

```agda
record Segment (⟨L,⊏⟩ : OrderStruct) : Type₁ where
  constructor seg
  L = ⟨L,⊏⟩ .fst
  _⊏_ = ⟨L,⊏⟩ .snd
  field
    ℓ : L
    O⁻ : {a : L} → a ⊏ ℓ → OrderStruct
```

**定义** 抽象树序数 (由自然数索引前段族索引)

```agda
module Tree (k : ℕ) (O⃗ : Vec OrderStruct k) (S : (k⁻ : Fin k) → Segment (lookup O⃗ k⁻)) where
```

互归纳定义

```agda
  data A : Type
  data R : A → A → Type

  R₁ : A → A → Type
  R₁ α β = ∥ R α β ∥₁
```

```agda
  module Seg (k⁻ : Fin k) where
    open Segment (S k⁻) public
    private variable
      a : L
      aℓ : a ⊏ ℓ

    Seq : a ⊏ ℓ → Type
    Seq aℓ = O⁻ aℓ .fst → A

    mono : Seq aℓ → Type
    mono {aℓ} f = ∀ {ν μ} → O⁻ aℓ .snd ν μ → R₁ (f ν) (f μ)
```

```agda
  data A where
    zero : A
    suc : A → A
    lim : (k⁻ : Fin k) → let open Seg k⁻ in
      (a : L) (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → A
```

```agda
  private variable α β : A
  data R where
    zero : R α (suc α)
    suc  : R α β → R α (suc β)
    lim  : (k⁻ : Fin k) → let open Seg k⁻ in
      (a : L) (aℓ : a ⊏ ℓ) {f : Seq aℓ} {mo : mono f} {ν : O⁻ aℓ .fst} →
      R α (f ν) → R α (lim k⁻ a aℓ f mo)
```

## CK序数层级

**定义** 等级结构

```agda
record LevelStruct : Type₁ where
  field
    ⟨L,⊏⟩ : OrderStruct
  L = ⟨L,⊏⟩ .fst
  _⊏_ = ⟨L,⊏⟩ .snd
  field
    ⊏-wf : WellFounded _⊏_
    ⊏-trans : Transitive _⊏_
    ⊏-prop : ∀ {a b} → isProp (a ⊏ b)
```

```agda
module CK (k : ℕ) (O⃗ : Vec OrderStruct k) (S : (k⁻ : Fin k) → Segment (lookup O⃗ k⁻)) (L̂ : LevelStruct) where
  open LevelStruct L̂
  open Tree (suc k) (⟨L,⊏⟩ ∷ O⃗) using (A ; R; zero; suc; lim)
  module W = WF.All ⊏-wf
  private variable
    a b c ℓ ℓ′ ℓ″ : L
    aℓ : a ⊏ ℓ
```

```agda
  seg-cons : (O⁻ : {a : L} → a ⊏ ℓ → OrderStruct) (k⁻ : Fin (suc k)) → Segment (lookup (⟨L,⊏⟩ ∷ O⃗) k⁻)
  seg-cons O⁻ zero = seg _ O⁻
  seg-cons _ (suc k⁻) = S k⁻

  ⟨U,R⟩⁻ : a ⊏ ℓ → OrderStruct
  ⟨U,R⟩⁻ = W.wfRecBuilder _ _ (λ _ O⁻ → A (seg-cons O⁻) , R (seg-cons O⁻)) _
```
