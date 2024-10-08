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
open import Cubical.Foundations.Prelude public renaming (_∎ to _≡∎)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Function public using (2-Constant)
open import Cubical.Data.Equality public using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
open import Cubical.HITs.PropositionalTruncation public
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; _∷_; lookup) renaming (map to map⃗)
open import Function public using (id; _∘_; _$_; flip)
open import Relation.Binary.Definitions public
open import Relation.Binary.Structures using (IsEquivalence)
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

## 准良序结构

**引理** 道路是等价关系.  

```agda
≡-isEquivalence : {a : Level} {A : Type a} → IsEquivalence {A = A} _≡_
≡-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = _∙_
  }
```

**引理** 可及关系是命题.  

```agda
isPropAcc : {a b : Level} {A : Type a} {R : A → A → Type b} {a : A} → isProp (Acc R a)
isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)
```

**定义** 局域三歧性

```agda
LocallyTrichotomous : {a b : Level} {A : Type a} (R : A → A → Type b) → Type (ℓ-max a b)
LocallyTrichotomous R = ∀ {x y z} → R x z → R y z → Tri (R x y) (x ≡ y) (R y x)
```

**定义** 典范性

```agda
Canonical : {a b : Level} {A : Type a} (R : A → A → Type b) → Type (ℓ-max a b)
Canonical R = ∀ {x y} → Σ (R x y → R x y) 2-Constant
```

**定义** 准良序结构

```agda
record W̅oset : Type₁ where
  constructor mk
  field
    A : Type
    _≺_ : A → A → Type
    A-set : isSet A
    ≺-set : ∀ {a b} → isSet (a ≺ b)
    ≺-cano : Canonical _≺_
    ≺-wf : WellFounded _≺_
    ≺-trans : Transitive _≺_
    ≺-trich : LocallyTrichotomous _≺_
```

### 命题关系

```agda
  _≺₁_ : A → A → Type
  _≺₁_ a b = ∥ a ≺ b ∥₁

  set : {a b : A} → a ≺₁ b → a ≺ b
  set = rec→Set ≺-set (fst ≺-cano) (snd ≺-cano)

  ≺₁-acc : ∀ {a} → Acc _≺_ a → Acc _≺₁_ a
  ≺₁-acc (acc r) = acc (rec isPropAcc (≺₁-acc ∘ r))

  ≺₁-wf : WellFounded _≺₁_
  ≺₁-wf = ≺₁-acc ∘ ≺-wf

  ≺₁-trans : Transitive _≺₁_
  ≺₁-trans = map2 ≺-trans

  ≺₁-trich : LocallyTrichotomous _≺₁_
  ≺₁-trich r s with ≺-trich (set r) (set s)
  ... | tri< a ¬b ¬c = tri< ∣ a ∣₁ ¬b (rec isProp⊥ ¬c)
  ... | tri≈ ¬a b ¬c = tri≈ (rec isProp⊥ ¬a) b (rec isProp⊥ ¬c)
  ... | tri> ¬a ¬b c = tri> (rec isProp⊥ ¬a) ¬b ∣ c ∣₁
```

### 导出性质

```agda
  ≺-resp-≡ : _≺_ Respects₂ _≡_
  ≺-resp-≡ = subst (_ ≺_) , subst (_≺ _)

  ≺₁-resp-≡ : _≺₁_ Respects₂ _≡_
  ≺₁-resp-≡ = subst (_ ≺₁_) , subst (_≺₁ _)

  ≺-irrefl : Irreflexive _≡_ _≺_
  ≺-irrefl = wf⇒irrefl ≺-resp-≡ sym ≺-wf

  ≺₁-irrefl : Irreflexive _≡_ _≺₁_
  ≺₁-irrefl = wf⇒irrefl ≺₁-resp-≡ sym ≺₁-wf

  ≺-asym : Asymmetric _≺_
  ≺-asym = wf⇒asym ≺-wf

  ≺₁-asym : Asymmetric _≺₁_
  ≺₁-asym = wf⇒asym ≺₁-wf
```

### 衍生非严格序

```agda
  open import Relation.Binary.Construct.StrictToNonStrict _≡_ _≺_
    as NonStrictRoad public using () renaming (_≤_ to infix 6 _≼_; <⇒≤ to ≺→≼)

  open import Relation.Binary.Construct.StrictToNonStrict _≡_ _≺₁_
    as NonStrictSubTree public using () renaming (_≤_ to infix 6 _≼₁_; <⇒≤ to ≺₁→≼₁)
```

```agda
  private variable a b : A
  ≼₁-prop : isProp (a ≼₁ b)
  ≼₁-prop = isProp⊎ squash₁ (A-set _ _) (flip ≺₁-irrefl)

  ≼→≼₁ : a ≼ b → a ≼₁ b
  ≼→≼₁ (inl r) = inl ∣ r ∣₁
  ≼→≼₁ (inr r) = inr r

  ≼₁→≼ : a ≼₁ b → a ≼ b
  ≼₁→≼ (inl r) = inl (set r)
  ≼₁→≼ (inr r) = inr r
```

```agda
  ≼-refl : Reflexive _≼_
  ≼-refl = NonStrictRoad.reflexive refl

  ≼-antisym : Antisymmetric _≡_ _≼_
  ≼-antisym = NonStrictRoad.antisym ≡-isEquivalence ≺-trans ≺-irrefl

  ≼-trans : Transitive _≼_
  ≼-trans = NonStrictRoad.trans ≡-isEquivalence ≺-resp-≡ ≺-trans

  ≺-≼-trans : Trans _≺_ _≼_ _≺_
  ≺-≼-trans = NonStrictRoad.<-≤-trans ≺-trans (fst ≺-resp-≡)

  ≼-≺-trans : Trans _≼_ _≺_ _≺_
  ≼-≺-trans = NonStrictRoad.≤-<-trans sym ≺-trans (snd ≺-resp-≡)
```

```agda
  ≼₁-refl : Reflexive _≼₁_
  ≼₁-refl = NonStrictSubTree.reflexive refl

  ≼₁-antisym : Antisymmetric _≡_ _≼₁_
  ≼₁-antisym = NonStrictSubTree.antisym ≡-isEquivalence ≺₁-trans ≺₁-irrefl

  ≼₁-trans : Transitive _≼₁_
  ≼₁-trans = NonStrictSubTree.trans ≡-isEquivalence ≺₁-resp-≡ ≺₁-trans

  ≺₁-≼₁-trans : Trans _≺₁_ _≼₁_ _≺₁_
  ≺₁-≼₁-trans = NonStrictSubTree.<-≤-trans ≺₁-trans (fst ≺₁-resp-≡)

  ≼₁-≺₁-trans : Trans _≼₁_ _≺₁_ _≺₁_
  ≼₁-≺₁-trans = NonStrictSubTree.≤-<-trans sym ≺₁-trans (snd ≺₁-resp-≡)
```

### 偏序结构

```agda
  open import Relation.Binary.Structures {A = A} _≡_

  ≺-isStrictPartialOrder : IsStrictPartialOrder _≺_
  ≺-isStrictPartialOrder = record
    { isEquivalence = ≡-isEquivalence
    ; irrefl = ≺-irrefl
    ; trans = ≺-trans
    ; <-resp-≈ = ≺-resp-≡ }

  ≺₁-isStrictPartialOrder : IsStrictPartialOrder _≺₁_
  ≺₁-isStrictPartialOrder = record
    { isEquivalence = ≡-isEquivalence
    ; irrefl = ≺₁-irrefl
    ; trans = ≺₁-trans
    ; <-resp-≈ = ≺₁-resp-≡ }
```

```agda
  ≼-isPreorder : IsPreorder _≼_
  ≼-isPreorder = record
    { isEquivalence = ≡-isEquivalence
    ; reflexive = inr
    ; trans = ≼-trans
    }

  ≼₁-isPreorder : IsPreorder _≼₁_
  ≼₁-isPreorder = record
    { isEquivalence = ≡-isEquivalence
    ; reflexive = inr
    ; trans = ≼₁-trans
    }

  ≼-isPartialOrder : IsPartialOrder _≼_
  ≼-isPartialOrder = record { isPreorder = ≼-isPreorder ; antisym = ≼-antisym }

  ≼₁-isPartialOrder : IsPartialOrder _≼₁_
  ≼₁-isPartialOrder = record { isPreorder = ≼₁-isPreorder ; antisym = ≼₁-antisym }
```

```agda
  module RoadReasoning where
    open import Relation.Binary.Reasoning.Base.Triple
      {_≈_ = _≡_} {_≤_ = _≼_} {_<_ = _≺_}
      ≼-isPreorder ≺-asym ≺-trans ≺-resp-≡ ≺→≼ ≺-≼-trans ≼-≺-trans
      public

  module SubTreeReasoning where
    open import Relation.Binary.Reasoning.Base.Triple
      {_≈_ = _≡_} {_≤_ = _≼₁_} {_<_ = _≺₁_}
      ≼₁-isPreorder ≺₁-asym ≺₁-trans ≺₁-resp-≡ ≺₁→≼₁ ≺₁-≼₁-trans ≼₁-≺₁-trans
      public
```
