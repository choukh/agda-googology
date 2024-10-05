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

## 基础结构

**定义** 序结构

```agda
OrderStruct : Type₁
OrderStruct = Σ Type λ A → A → A → Type
```

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

**定义** 由序结构索引的序结构族前段

```agda
record Segment (⟨L,⊏⟩ : OrderStruct) : Type₁ where
  constructor seg
  L = ⟨L,⊏⟩ .fst
  _⊏_ = ⟨L,⊏⟩ .snd
  field
    ℓ : L
    S : {a : L} → a ⊏ ℓ → OrderStruct
```

**定义** 自然数索引的前段族

```agda
Segments : {k : ℕ} (O⃗ : Vec OrderStruct k) → Type₁
Segments {k} O⃗ = (k⁻ : Fin k) → Segment (lookup O⃗ k⁻)
```

**定义** 前段族的构造方法

```agda
_∷ˢ_ : {O@(L , _⊏_) : OrderStruct} {ℓ : L} (S : {a : L} → a ⊏ ℓ → OrderStruct)
       {k : ℕ} {O⃗ : Vec OrderStruct k} (S⃗ : Segments O⃗) → Segments (O ∷ O⃗)
(S ∷ˢ S⃗) zero = seg _ S
(S ∷ˢ S⃗) (suc k) = S⃗ k
```

## 抽象树序数

**定义** 抽象树序数 (由前段族索引)

```agda
module Tree (k : ℕ) (O⃗ : Vec OrderStruct k) (S⃗ : Segments O⃗) where
```

互归纳定义

```agda
  data O : Type
  data _<_ : O → O → Type

  _<₁_ : O → O → Type
  α <₁ β = ∥ α < β ∥₁
```

```agda
  module Seg (k⁻ : Fin k) where
    open Segment (S⃗ k⁻) public
    private variable
      a : L
      aℓ : a ⊏ ℓ

    Seq : a ⊏ ℓ → Type
    Seq aℓ = S aℓ .fst → O

    mono : Seq aℓ → Type
    mono {aℓ} f = ∀ {ν μ} → S aℓ .snd ν μ → f ν <₁ f μ
```

```agda
  data O where
    zero : O
    suc : O → O
    lim : (k⁻ : Fin k) → let open Seg k⁻ in
      (a : L) (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → O
```

```agda
  private variable α β : O
  data _<_ where
    zero : α < suc α
    suc  : α < β → α < suc β
    lim  : {k⁻ : Fin k} → let open Seg k⁻ in
      {a : L} {aℓ : a ⊏ ℓ} {f : Seq aℓ} {mo : mono f} {ν : S aℓ .fst} →
      α < f ν → α < lim k⁻ a aℓ f mo
```

### 路径的良基性

```agda
  <-trans : Transitive _<_
  <-trans r zero = suc r
  <-trans r (suc s) = suc (<-trans r s)
  <-trans r (lim s) = lim (<-trans r s)

  <-acc : α < β → Acc _<_ α
  <-acc zero = acc λ s → <-acc s
  <-acc (suc r) = acc λ s → <-acc (<-trans s r)
  <-acc (lim r) = acc λ s → <-acc (<-trans s r)

  <-wf : WellFounded _<_
  <-wf _ = <-acc zero
```

```agda
  isPropAcc : isProp (Acc _<₁_ α)
  isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)

  <₁-acc : α <₁ β → Acc _<₁_ α
  <₁-acc ∣ zero  ∣₁ = acc λ r → <₁-acc r
  <₁-acc ∣ suc r ∣₁ = acc λ s → <₁-acc (map2 <-trans s ∣ r ∣₁)
  <₁-acc ∣ lim r ∣₁ = acc λ s → <₁-acc (map2 <-trans s ∣ r ∣₁)
  <₁-acc (squash₁ p q i) = isPropAcc (<₁-acc p) (<₁-acc q) i

  <₁-wf : WellFounded _<₁_
  <₁-wf _ = <₁-acc ∣ zero ∣₁
```

## CK序数层级

```agda
module CK (k : ℕ) (O⃗ : Vec OrderStruct k) (S⃗ : Segments O⃗) (L̂ : LevelStruct) where
  open LevelStruct L̂
  open Tree (suc k) (⟨L,⊏⟩ ∷ O⃗) using (O ; _<_; zero; suc; lim)
  module W = WF.All ⊏-wf
  private variable
    a b c ℓ ℓ′ ℓ″ : L
    aℓ : a ⊏ ℓ
```

```agda
  ⟨O,<⟩⁻ : a ⊏ ℓ → OrderStruct
  ⟨O,<⟩⁻ = W.wfRecBuilder _ _ (λ _ S → O (S ∷ˢ S⃗) , _<_ (S ∷ˢ S⃗)) _

  ⟨O,<⟩ : L → OrderStruct
  ⟨O,<⟩ = W.wfRec _ _ λ _ S → O (S ∷ˢ S⃗) , _<_ (S ∷ˢ S⃗)
```
