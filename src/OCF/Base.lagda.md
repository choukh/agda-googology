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

## 准良序结构

**引理** 可及关系是命题.  

```agda
isPropAcc : {a b : Level} {A : Type a} {R : A → A → Type b} {a : A} → isProp (Acc R a)
isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)
```

**定义** 局域三歧性.  

```agda
LocallyTrichotomous : {a b : Level} {A : Type a} (R : A → A → Type b) → Type (ℓ-max a b)
LocallyTrichotomous R = ∀ {x y z} → R x z → R y z → Tri (R x y) (x ≡ y) (R y x)
```

**定义** 典范性.  

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
