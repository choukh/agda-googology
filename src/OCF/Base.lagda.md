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

**引理** 可及关系是命题.  

```agda
isPropAcc : {a b : Level} {A : Type a} {R : A → A → Type b} {a : A} → isProp (Acc R a)
isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)
```

**定义** 良基传递结构

```agda
record WfTrans : Type₁ where
  constructor mk
  field
    A : Type
    R : A → A → Type
    R-wf : WellFounded R
    R-trans : Transitive R

  R₁ : A → A → Type
  R₁ a b = ∥ R a b ∥₁

  R₁-trans : Transitive R₁
  R₁-trans = map2 R-trans

  R₁-acc : ∀ {a} → Acc R a → Acc R₁ a
  R₁-acc (acc r) = acc (rec isPropAcc (R₁-acc ∘ r))

  R₁-wf : WellFounded R₁
  R₁-wf = R₁-acc ∘ R-wf
```

**定义** 抽象树序数

```agda
module Tree ((mk Lv _⊏_ _ _) : WfTrans) (ℓ : Lv) (Rec : ∀ {a} → a ⊏ ℓ → WfTrans) where
  private variable
    a : Lv
    aℓ : a ⊏ ℓ
```

```agda
  data O : Type
  data _<_ : O → O → Type

  _<₁_ : O → O → Type
  α <₁ β = ∥ α < β ∥₁
```

```agda
  module _ (aℓ : a ⊏ ℓ) where
    open WfTrans (Rec aℓ) public using () renaming (A to O⁻)
  module _ {aℓ : a ⊏ ℓ} where
    open WfTrans (Rec aℓ) public using () renaming (R to _<⁻_)

  Seq : a ⊏ ℓ → Type
  Seq aℓ = O⁻ aℓ → O

  mono : Seq aℓ → Type
  mono {aℓ} f = ∀ {ν μ} → ν <⁻ μ → f ν <₁ f μ
```

```agda
  data O where
    zero : O
    suc : O → O
    lim : (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → O
```

```agda
  private variable α β : O
  data _<_ where
    zero : α < suc α
    suc  : α < β → α < suc β
    lim  : {f : Seq aℓ} {mo : mono f} {ν : O⁻ aℓ} → α < f ν → α < lim aℓ f mo
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

**定理** 抽象树序数构成良基传递结构.  

```agda
  wfTrans : WfTrans
  wfTrans = mk O _<_ <-wf <-trans
```
