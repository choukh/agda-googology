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

**定义** 良基结构

```agda
record WfStruct : Type₁ where
  constructor wf
  field
    A : Type
    R : A → A → Type
    R-wf : WellFounded R
```

**定义** 由良基结构索引的良基结构族前段

```agda
record Segment (L : WfStruct) : Type₁ where
  constructor seg
  open WfStruct L public renaming (A to Lv; R to _⊏_; R-wf to ⊏-wf)
  field
    ℓ : Lv
    S : {a : Lv} → a ⊏ ℓ → WfStruct
```

**定义** 自然数索引的前段族

```agda
Segments : {k : ℕ} (L⃗ : Vec WfStruct k) → Type₁
Segments {k} L⃗ = (k⁻ : Fin k) → Segment (lookup L⃗ k⁻)
```

**定义** 前段族的构造方法

```agda
_∷ˢ_ : {L@(wf Lv _⊏_ _) : WfStruct} {ℓ : Lv} (S : {a : Lv} → a ⊏ ℓ → WfStruct)
       {k : ℕ} {L⃗ : Vec WfStruct k} (S⃗ : Segments L⃗) → Segments (L ∷ L⃗)
(S ∷ˢ S⃗) zero = seg _ S
(S ∷ˢ S⃗) (suc k) = S⃗ k
```

## 抽象树序数

**定义** 抽象树序数 (由前段族索引)

```agda
module Tree (k : ℕ) (L⃗ : Vec WfStruct k) (S⃗ : Segments L⃗) where
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
      a : Lv
      aℓ : a ⊏ ℓ

    Seq : a ⊏ ℓ → Type
    Seq aℓ = WfStruct.A (S aℓ) → O

    mono : Seq aℓ → Type
    mono {aℓ} f = ∀ {ν μ} → WfStruct.R (S aℓ) ν μ → f ν <₁ f μ
```

```agda
  data O where
    zero : O
    suc : O → O
    lim : (k⁻ : Fin k) → let open Seg k⁻ in
      (a : Lv) (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → O
```

```agda
  private variable α β : O
  data _<_ where
    zero : α < suc α
    suc  : α < β → α < suc β
    lim  : {k⁻ : Fin k} → let open Seg k⁻ in
      {a : Lv} {aℓ : a ⊏ ℓ} {f : Seq aℓ} {mo : mono f} {ν : WfStruct.A (S aℓ)} →
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

**定理** 抽象树序数构成良基结构.  

```agda
  tree : WfStruct
  tree = wf O _<₁_ <₁-wf
```

## CK序数层级

```agda
module CK (k : ℕ) (L⃗ : Vec WfStruct k) (S⃗ : Segments L⃗) (L : WfStruct) where
  open WfStruct L renaming (A to Lv; R to _⊏_; R-wf to ⊏-wf)
  module T = Tree (suc k) (L ∷ L⃗)
  open T using (zero; suc; lim)
  module W = WF.All ⊏-wf
  private variable
    a b c ℓ ℓ′ ℓ″ : Lv
    aℓ : a ⊏ ℓ
```

```agda
  tree⁻ : a ⊏ ℓ → WfStruct
  tree⁻ = W.wfRecBuilder _ _ (λ _ S → T.tree (S ∷ˢ S⃗)) _

  tree : Lv → WfStruct
  tree = W.wfRec _ _ λ _ S → T.tree (S ∷ˢ S⃗)
```
