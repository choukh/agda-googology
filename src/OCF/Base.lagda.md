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
  hiding (lift) renaming (_∎ to _≡∎)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.Structure public
open import Cubical.Data.Equality public using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
open import Cubical.HITs.PropositionalTruncation public
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; _∷_; lookup) renaming (map to map⃗)
open import Function public using (id; _∘_; _∘₂_; _$_; flip; case_of_)
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
    _<_ : A → A → Type
    a : A
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
  isPropAcc : isProp (Acc _<_ a)
  isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)
```

**定义** 良基传递结构

```agda
record WfTrans : Type₁ where
  constructor mk
  field
    A : Type
    _<_ : A → A → Type
    <-wf : WellFounded _<_
    <-trans : Transitive _<_
```

```agda
  private variable a : A

  _<₁_ : A → A → Type
  _<₁_ = ∥_∥₁ ∘₂ _<_

  <₁-acc : Acc _<_ a → Acc _<₁_ a
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

## 抽象树序数

```agda
module Tree (L : WfTrans) where
  open WfTrans L using () renaming (A to Lv; _<₁_ to _⊏_)
  module _ (ℓ : Lv) (IH : ∀ {a} → a ⊏ ℓ → WfTrans) where
    private variable
      a : Lv
      aℓ : a ⊏ ℓ
    module _ (aℓ : a ⊏ ℓ) where
      open WfTrans (IH aℓ) public using () renaming (A to O⁻)
    module _ {aℓ : a ⊏ ℓ} where
      open WfTrans (IH aℓ) public using () renaming (_<_ to _<⁻_)
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
      lim : (aℓ : a ⊏ ℓ) (f : Seq aℓ) (mo : mono f) → O
```

```agda
    private variable α β γ : O
    data _<_ where
      zero : α < suc α
      suc  : α < β → α < suc β
      lim  : {aℓ : a ⊏ ℓ} {f : Seq aℓ} {mo : mono f} {ν : O⁻ aℓ} → α < f ν → α < lim aℓ f mo
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
    coe-id {aℓ} {ν} = subst (λ p → subst O⁻ p ν ≡ ν) (isProp→isSet squash₁ _ _ _ _) (fromPathP refl)
```

```agda
    module _
      {aℓᶠ : a ⊏ ℓ} {f : O⁻ aℓᶠ → O} {moᶠ : mono f}
      {aℓᵍ : a ⊏ ℓ} {g : O⁻ aℓᵍ → O} {moᵍ : mono g}
      (p : (ν : O⁻ aℓᶠ) → f ν ≡ g (coe ν))
      where

      limExt : lim aℓᶠ f moᶠ ≡ lim aℓᵍ g moᵍ
      limExt with (pathToEq $ squash₁ aℓᶠ aℓᵍ)
      ... | rfl = cong₂ (lim aℓᶠ) (funExt λ ν → subst (λ x → f ν ≡ g x) coe-id (p ν)) (toPathP $ mono-prop _ _)
```

### 良基传递性

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

**定理** 抽象树序数构成良基传递结构.  

```agda
    tree : WfTrans
    tree = mk O _<_ <-wf <-trans
```

```agda
open Tree using (zero; suc; lim) public
```

## 抽象CK序数层级

```agda
module CK (L : WfTrans) where
  open WfTrans L using () renaming (A to Lv; _<₁_ to _⊏_; <₁-wf to ⊏-wf; <₁-trans to ⊏-trans)
  open Tree L using (tree)
  module W = WF.All ⊏-wf
  private variable
    a b c ℓ ℓ′ ℓ″ : Lv
    aℓ : a ⊏ ℓ
```

```agda
  ck⁻ : a ⊏ ℓ → WfTrans
  ck⁻ = W.wfRecBuilder _ _ (λ _ → tree _) _

  ck : Lv → WfTrans
  ck = W.wfRec _ _ λ _ → tree _
```

```agda
  module _ (ℓ : Lv) where
    open WfTrans (ck ℓ) public using () renaming (A to O)
  module _ {ℓ : Lv} where
    open WfTrans (ck ℓ) public using (_<_)
```

### 变体表示

```agda
  module _ (aℓ : a ⊏ ℓ) where
    open WfTrans (ck⁻ aℓ) public using () renaming (A to O⁻)
  module _ {aℓ : a ⊏ ℓ} where
    open WfTrans (ck⁻ aℓ) public using () renaming (_<_ to _<⁻_)
```

```agda
  module _ {aℓ : a ⊏ ℓ} where
    tonePath : ck⁻ aℓ ≡ ck a
    tonePath = eqToPath $ FixPoint.wfRecBuilder-wfRec ⊏-wf _ _
      (λ ℓ IH → Eq.cong (tree ℓ) (pathToEq λ i aℓ → eqToPath (IH aℓ) i)) _

    ♯ : O⁻ aℓ → O a
    ♯ = transport (cong WfTrans.A tonePath)

    ♭ : O a → O⁻ aℓ
    ♭ = transport⁻ (cong WfTrans.A tonePath)

    ♭∘♯ : {α : O⁻ aℓ} → ♭ (♯ α) ≡ α
    ♭∘♯ = transport⁻Transport _ _

    ♯∘♭ : {α : O a} → ♯ (♭ α) ≡ α
    ♯∘♭ = transportTransport⁻ _ _
```

```agda
  ♮⟨_,_⟩ : (p : a ⊏ ℓ) (q : a ⊏ ℓ′) → O⁻ p → O⁻ q
  ♮⟨ _ , _ ⟩ = ♭ ∘ ♯

  ♮ : {p : a ⊏ ℓ} {q : a ⊏ ℓ′} → O⁻ p → O⁻ q
  ♮ = ♮⟨ _ , _ ⟩

  ♮-comp : {p : a ⊏ ℓ} {q : a ⊏ ℓ′} {r : a ⊏ ℓ″} {α : O⁻ p}
    → ♮⟨ q , r ⟩ (♮⟨ p , q ⟩ α) ≡ ♮⟨ p , r ⟩ α
  ♮-comp = cong ♭ ♯∘♭

  ♮-invo : {p : a ⊏ ℓ} {q : a ⊏ ℓ′} {α : O⁻ p}
    → ♮⟨ q , p ⟩ (♮⟨ p , q ⟩ α) ≡ α
  ♮-invo = ♮-comp ∙ ♭∘♯
```

```agda
  module _ {aℓ : a ⊏ ℓ} where
    <-distrib-transp : (λ α β → ♭ {aℓ = aℓ} α <⁻ ♭ β) ≡ subst (λ A → A → A → Type) (cong WfTrans.A tonePath) (_<⁻_ {aℓ = aℓ})
    <-distrib-transp = J (λ _ p → (λ α β → transport⁻ p α <⁻ transport⁻ p β) ≡ subst (λ A → A → A → Type) p _<⁻_) refl (cong WfTrans.A tonePath)

    ♭-inj< : {α β : O a} → ♭ {aℓ = aℓ} α <⁻ ♭ β ≡ α < β
    ♭-inj< = (<-distrib-transp ∙ fromPathP (cong WfTrans._<_ tonePath)) ≡$ _ ≡$ _

    ♯-inj< : {α β : O⁻ aℓ} → ♯ α < ♯ β ≡ α <⁻ β
    ♯-inj< {α} {β} = subst2 (λ x y → ♯ α < ♯ β ≡ x <⁻ y) ♭∘♯ ♭∘♯ (sym ♭-inj<)

  ♮-inj< : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α β : O⁻ aℓ} → ♮⟨ aℓ , aℓ′ ⟩ α <⁻ ♮ β ≡ α <⁻ β
  ♮-inj< = ♭-inj< ∙ ♯-inj<
```

### 层级的提升

```agda
  mutual
    lift : a ⊏ b → O a → O b
    lift ab zero = zero
    lift ab (suc α) = suc (lift ab α)
    lift ab (lim xa f mo) = lim (⊏-trans xa ab)
      (λ ν → lift ab (f $ ♮⟨ ⊏-trans xa ab , xa ⟩ ν)) (map lift-mono ∘ mo ∘ transport⁻ ♮-inj<)

    lift-mono : {ab : a ⊏ b} {α β : O a} → α < β → lift ab α < lift ab β
    lift-mono zero = zero
    lift-mono (suc r) = suc (lift-mono r)
    lift-mono (lim {f} r) = lim (lift-mono $ subst⁻ (λ x → _ < f x) ♮-invo r)
```

提升的复合

```agda
  lift-comp : {ab : a ⊏ b} {bc : b ⊏ c} {ac : a ⊏ c} {α : O a}
            → lift ac α ≡ lift bc (lift ab α)
  lift-comp {α = zero} = refl
  lift-comp {α = suc α} = cong suc (lift-comp {α = α})
  lift-comp {c} {ab} {bc} {ac} {α = lim aℓ f _} = Tree.limExt _ _ _ λ ν →
    subst2 (λ x y → lift ac (f x) ≡ lift bc (lift ab (f y)))
      --(subst (λ x → ♮ (♮ x) ≡ ♮ ν) (sym {!   !}) {!  ♮-comp !})
      (♮-comp ∙ {! ⊏-trans (⊏-trans aℓ ab) bc !})
      refl lift-comp
```

## CK序数层级
