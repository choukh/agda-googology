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
open import Function public using (id; _∘_; _∘₂_; _$_; flip)
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

## 序结构

```agda
module _ where
  private variable
    A : Type
    a : A
    R : A → A → Type
```

**引理** 道路是等价关系.  

```agda
  ≡-isEquivalence : IsEquivalence {A = A} _≡_
  ≡-isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = _∙_
    }
```

**引理** 可及关系是命题.  

```agda
  isPropAcc : isProp (Acc R a)
  isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)
```

**定义** 局域三歧性

```agda
  LocallyTrichotomous : (R : A → A → Type) → Type
  LocallyTrichotomous R = ∀ {x y z} → R x z → R y z → Tri (R x y) (x ≡ y) (R y x)
```

**定义** 典范性

```agda
  Canonical : (R : A → A → Type) → Type
  Canonical R = ∀ {x y} → Σ (R x y → R x y) 2-Constant
```

**定义** 良基传递结构

```agda
  record IsWfTrans (_<_ : A → A → Type) : Type₁ where
    constructor mk
    field
      <-wf : WellFounded _<_
      <-trans : Transitive _<_
```

```agda
    _<₁_ : A → A → Type
    _<₁_ = ∥_∥₁ ∘₂ _<_

    <₁-acc : ∀ {a} → Acc _<_ a → Acc _<₁_ a
    <₁-acc (acc r) = acc (rec isPropAcc (<₁-acc ∘ r))

    <₁-wf : WellFounded _<₁_
    <₁-wf = <₁-acc ∘ <-wf

    <₁-trans : Transitive _<₁_
    <₁-trans = map2 <-trans
```

```agda
    <-resp-≡ : _<_ Respects₂ _≡_
    <-resp-≡ = subst (_ <_) , subst (_< _)

    <-irrefl : Irreflexive _≡_ _<_
    <-irrefl = wf⇒irrefl <-resp-≡ sym <-wf

    <-asym : Asymmetric _<_
    <-asym = wf⇒asym <-wf
```

```agda
    open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
      as NonStrict public using (_≤_) renaming (<⇒≤ to <→≤)
```

```agda
    ≤-refl : Reflexive _≤_
    ≤-refl = NonStrict.reflexive refl

    ≤-antisym : Antisymmetric _≡_ _≤_
    ≤-antisym = NonStrict.antisym ≡-isEquivalence <-trans <-irrefl

    ≤-trans : Transitive _≤_
    ≤-trans = NonStrict.trans ≡-isEquivalence <-resp-≡ <-trans

    <-≤-trans : Trans _<_ _≤_ _<_
    <-≤-trans = NonStrict.<-≤-trans <-trans (fst <-resp-≡)

    ≤-<-trans : Trans _≤_ _<_ _<_
    ≤-<-trans = NonStrict.≤-<-trans sym <-trans (snd <-resp-≡)
```

```agda
    open import Relation.Binary.Structures {A = A} _≡_

    <-isStrictPartialOrder : IsStrictPartialOrder _<_
    <-isStrictPartialOrder = record
      { isEquivalence = ≡-isEquivalence
      ; irrefl = <-irrefl
      ; trans = <-trans
      ; <-resp-≈ = <-resp-≡ }

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder = record
      { isEquivalence = ≡-isEquivalence
      ; reflexive = inr
      ; trans = ≤-trans
      }

    ≤-isPartialOrder : IsPartialOrder _≤_
    ≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }

    module Reasoning where
      open import Relation.Binary.Reasoning.Base.Triple
        {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
        ≤-isPreorder <-asym <-trans <-resp-≡ <→≤ <-≤-trans ≤-<-trans
        public
```

**定义** 准良序集

```agda
record W̅oset : Type₁ where
  constructor mk
  field
    A : Type
    _<_ : A → A → Type
    <-isWfTrans : IsWfTrans _<_

    A-set : isSet A
    <-set : ∀ {a b} → isSet (a < b)
    <-cano : Canonical _<_
    <-trich : LocallyTrichotomous _<_
```

```agda
  open IsWfTrans <-isWfTrans public
  open IsWfTrans (mk <₁-wf <₁-trans) public using ()
    renaming (_≤_ to _≤₁_; <-irrefl to <₁-irrefl)
  private variable a b : A
```

```agda
  ≤₁-prop : isProp (a ≤₁ b)
  ≤₁-prop = isProp⊎ squash₁ (A-set _ _) (flip <₁-irrefl)

  ≤→≤₁ : a ≤ b → a ≤₁ b
  ≤→≤₁ (inl r) = inl ∣ r ∣₁
  ≤→≤₁ (inr r) = inr r
```

```agda
  set : a <₁ b → a < b
  set = rec→Set <-set (fst <-cano) (snd <-cano)

  ≤₁→≤ : a ≤₁ b → a ≤ b
  ≤₁→≤ (inl r) = inl (set r)
  ≤₁→≤ (inr r) = inr r

  <₁-trich : LocallyTrichotomous _<₁_
  <₁-trich r s with <-trich (set r) (set s)
  ... | tri< a ¬b ¬c = tri< ∣ a ∣₁ ¬b (rec isProp⊥ ¬c)
  ... | tri≈ ¬a b ¬c = tri≈ (rec isProp⊥ ¬a) b (rec isProp⊥ ¬c)
  ... | tri> ¬a ¬b c = tri> (rec isProp⊥ ¬a) ¬b ∣ c ∣₁
```

## 抽象树序数

```agda
module Tree (L : W̅oset) where
  open W̅oset L using () renaming (A to Lv; _<₁_ to _⊏_; <₁-trich to ⊏-trich)
  module _ (ℓ : Lv) (IH : ∀ {a} → a ⊏ ℓ → W̅oset) where
    private variable
      a : Lv
      aℓ : a ⊏ ℓ
    module _ (aℓ : a ⊏ ℓ) where
      open W̅oset (IH aℓ) public using () renaming (A to O⁻)
    module _ {aℓ : a ⊏ ℓ} where
      open W̅oset (IH aℓ) public using () renaming (_<_ to _<⁻_)
```

```agda
    data O : Type
    data _<_ : O → O → Type

    _<₁_ : O → O → Type
    α <₁ β = ∥ α < β ∥₁
```

```agda
    Seq : a ⊏ ℓ → Type
    Seq aℓ = O⁻ aℓ → O

    mono : Seq aℓ → Type
    mono {aℓ} f = ∀ {ν μ} → ν <⁻ μ → f ν <₁ f μ
```

```agda
    data O where
      zero : O
      suc : O → O
      lim : (a : Lv) (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → O
```

```agda
    private variable α β γ : O
    data _<_ where
      zero : α < suc α
      suc  : α < β → α < suc β
      lim  : {aℓ : a ⊏ ℓ} {f : Seq aℓ} {mo : mono f} {ν : O⁻ aℓ} → α < f ν → α < lim _ _ f mo
```

### 极限的外延性

```agda
    mono-prop : {f : Seq aℓ} → isProp (mono f)
    mono-prop = isPropImplicitΠ2 λ _ _ → isProp→ squash₁
```

```agda
    coe : {aℓ₁ aℓ₂ : a ⊏ ℓ} → O⁻ aℓ₁ → O⁻ aℓ₂
    coe = subst O⁻ (squash₁ _ _)

    coe-id : {aℓ : a ⊏ ℓ} {ν : O⁻ aℓ} → coe ν ≡ ν
    coe-id = {!   !}
```

```agda
    module _
      {aℓᶠ : a ⊏ ℓ} {f : O⁻ aℓᶠ → O} {moᶠ : mono f}
      {aℓᵍ : a ⊏ ℓ} {g : O⁻ aℓᵍ → O} {moᵍ : mono g}
      (p : (ν : O⁻ aℓᶠ) → f ν ≡ g (coe ν))
      where

      limExt : lim a aℓᶠ f moᶠ ≡ lim a aℓᵍ g moᵍ
      limExt with (pathToEq $ squash₁ aℓᶠ aℓᵍ)
      ... | rfl = cong₂ (lim a aℓᶠ) (funExt λ ν → subst (λ x → f ν ≡ g x) coe-id (p ν)) (toPathP $ mono-prop _ _)
```

### 准良序性

**引理** $<$ 是传递关系.  

```agda
    <-trans : Transitive _<_
    <-trans r zero = suc r
    <-trans r (suc s) = suc (<-trans r s)
    <-trans r (lim s) = lim (<-trans r s)
```

**引理** $<$ 是良基关系.  

```agda
    <-acc : α < β → Acc _<_ α
    <-acc zero = acc λ s → <-acc s
    <-acc (suc r) = acc λ s → <-acc (<-trans s r)
    <-acc (lim r) = acc λ s → <-acc (<-trans s r)

    <-wf : WellFounded _<_
    <-wf _ = <-acc zero
```

**引理** $O$ 是集合.  

```agda
    O-set : isSet O
    O-set = {!   !}
```

```agda
    open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<₁_
      as NonStrictSubTree public using () renaming (_≤_ to infix 6 _≤₁_; <⇒≤ to <→≤₁)
```

```agda
    <₁-connex-pre : α < γ → β < γ → α <₁ β ⊎ β ≤₁ α
    <₁-connex-pre zero    zero    = inr (inr refl)
    <₁-connex-pre zero    (suc s) = inr (inl ∣ s ∣₁)
    <₁-connex-pre (suc r) zero    = inl ∣ r ∣₁
    <₁-connex-pre (suc r) (suc s) = <₁-connex-pre r s
    <₁-connex-pre (lim {aℓ} r) (lim {aℓ = bℓ} s) with ⊏-trich aℓ bℓ
    ... | tri< a ¬b ¬c = {!   !}
    ... | tri≈ ¬a b ¬c = {!   !}
    ... | tri> ¬a ¬b c = {!   !}
```

**引理** $<$ 是局域三歧关系.  

```agda
    <-trich : LocallyTrichotomous _<_
    <-trich = {!   !}
```

**定理** 抽象树序数构成准良序结构.  

```agda
    tree : W̅oset
    tree = mk O _<_ (mk <-wf <-trans) O-set {!   !} {!   !} <-trich
```

```agda
open Tree using (zero; suc; lim) public
```
