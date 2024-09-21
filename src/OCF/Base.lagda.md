---
title: 形式化大数数学 (3.0 - 高阶递归序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 高阶递归序数)

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
  hiding (Level; Lift; lift) renaming (_∎ to _≡∎)
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
open import Function public using (id; _∘_; _$_; _⟨_⟩_)
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

## 基本结构

**定义** 序结构

```agda
OrderStruct : Type₁
OrderStruct = Σ Type λ A → A → A → Type
```

**定义** 等级结构

```agda
record LevelStruct : Type₁ where
  field
    Lv : Type
    _⊏_ : Lv → Lv → Type
    ⊏-wf : WellFounded _⊏_
    ⊏-trans : Transitive _⊏_
    ⊏-prop : ∀ {a b} → isProp (a ⊏ b)
```

## 层级

```agda
module Hierarchy {L : LevelStruct} where
  open LevelStruct L
  private variable
    a b ℓ ℓ′ ℓ″ : Lv
    aℓ : a ⊏ ℓ
```

### 定义的第1步: 互递归

```agda
  module O (ℓ : Lv) (O⁻ : ∀ {a} → a ⊏ ℓ → OrderStruct) where
    data A : Type
    data R : A → A → Type

    R₁ : A → A → Type
    R₁ α β = ∥ R α β ∥₁
```

```agda
    Seq : (aℓ : a ⊏ ℓ) → Type
    Seq aℓ = O⁻ aℓ .fst → A

    mono : Seq aℓ → Type
    mono {aℓ} f = ∀ {ν μ} → O⁻ aℓ .snd ν μ → R₁ (f ν) (f μ)
```

```agda
    data A where
      zero : A
      suc : A → A
      lim : (aℓ : a ⊏ ℓ) (f : O⁻ aℓ .fst → A) (mᶠ : mono f) → A
```

```agda
    private variable α β : A
    data R where
      zero : R α (suc α)
      suc  : R α β → R α (suc β)
      lim  : {f : O⁻ aℓ .fst → A} {mᶠ : mono f} {ν : O⁻ aℓ .fst} → R α (f ν) → R α (lim aℓ f mᶠ)
```

```agda
  open O using (zero; suc; lim) public
```

### 定义的第2步: 强归纳

```agda
  module _ where
    open WF.All ⊏-wf

    OrdStr⁻ : a ⊏ ℓ → OrderStruct
    OrdStr⁻ = wfRecBuilder _ _ (λ ℓ o → O.A ℓ o , O.R ℓ o) _

    OrdStr : Lv → OrderStruct
    OrdStr = wfRec _ _ (λ ℓ o → O.A ℓ o , O.R ℓ o)
```

```agda
  Ord : Lv → Type
  Ord ℓ = OrdStr ℓ .fst
  private variable α β : Ord ℓ

  _<_ : Ord ℓ → Ord ℓ → Type; infix 6 _<_
  _<_ = OrdStr _ .snd

  _<₁_ : Ord ℓ → Ord ℓ → Type; infix 6 _<₁_
  α <₁ β = ∥ α < β ∥₁
```

### 变体表示

```agda
  Ord⁻ : a ⊏ ℓ → Type
  Ord⁻ aℓ = OrdStr⁻ aℓ .fst

  _<⁻_ : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type; infix 6 _<⁻_
  _<⁻_ {aℓ} = OrdStr⁻ aℓ .snd
```

```agda
  module _ {aℓ : a ⊏ ℓ} where
    opaque
      OrdStrP : {aℓ : a ⊏ ℓ} → OrdStr⁻ aℓ ≡ OrdStr a
      OrdStrP = eqToPath $ FixPoint.wfRecBuilder-wfRec ⊏-wf _ _ (λ ℓ o → pathToEq $ ΣPathP $
        cong (O.A ℓ) (λ i aℓ → eqToPath (o aℓ) i) ,
        cong (O.R ℓ) (λ i aℓ → eqToPath (o aℓ) i)) _

    OrdP : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ ≡ Ord a
    OrdP = PathPΣ OrdStrP .fst

    RoadP : {aℓ : a ⊏ ℓ} → PathP (λ i → OrdP i → OrdP i → Type) (_<⁻_ {aℓ = aℓ}) _<_
    RoadP = PathPΣ OrdStrP .snd
```

```agda
    ♯ : Ord⁻ aℓ → Ord a
    ♯ = transport OrdP

    ♭ : Ord a → Ord⁻ aℓ
    ♭ = transport⁻ OrdP

    ♭♯ : {α : Ord⁻ aℓ} → ♭ (♯ α) ≡ α
    ♭♯ = transport⁻Transport _ _

    ♯♭ : {α : Ord a} → ♯ (♭ α) ≡ α
    ♯♭ = transportTransport⁻ _ _
```

```agda
  ♮$ : (from : a ⊏ ℓ) (to : a ⊏ ℓ′) → Ord⁻ from → Ord⁻ to
  ♮$ _ _ = ♭ ∘ ♯

  ♮ : {from : a ⊏ ℓ} {to : a ⊏ ℓ′} → Ord⁻ from → Ord⁻ to
  ♮ = ♮$ _ _

  ♮-comp : {p : a ⊏ ℓ} {q : a ⊏ ℓ′} {r : a ⊏ ℓ″} {α : Ord⁻ p}
        → ♮$ q r (♮$ p q α) ≡ ♮$ p r α
  ♮-comp = cong ♭ ♯♭

  ♮-invo : {from : a ⊏ ℓ} {to : a ⊏ ℓ′} {α : Ord⁻ from}
        → ♮$ to from (♮$ from to α) ≡ α
  ♮-invo = ♮-comp ∙ ♭♯
```

```agda
  module _ {aℓ : a ⊏ ℓ} where
    <-distrib-transp : (λ α β → ♭ {aℓ = aℓ} α <⁻ ♭ β) ≡ subst (λ A → A → A → Type) OrdP (_<⁻_ {aℓ = aℓ})
    <-distrib-transp = J (λ _ p → (λ α β → transport⁻ p α <⁻ transport⁻ p β) ≡ subst (λ A → A → A → Type) p _<⁻_) refl OrdP

    ♭-inj< : {α β : Ord a} → ♭ {aℓ = aℓ} α <⁻ ♭ β ≡ α < β
    ♭-inj< = (<-distrib-transp ∙ fromPathP RoadP) ≡$ _ ≡$ _

    ♯-inj< : {α β : Ord⁻ aℓ} → ♯ α < ♯ β ≡ α <⁻ β
    ♯-inj< {α} {β} = subst2 (λ x y → ♯ α < ♯ β ≡ x <⁻ y) ♭♯ ♭♯ (sym ♭-inj<)

  ♮-inj< : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α β : Ord⁻ aℓ} → ♮$ aℓ aℓ′ α <⁻ ♮ β ≡ α <⁻ β
  ♮-inj< = ♭-inj< ∙ ♯-inj<
```

### 极限的外延性

```agda
  Seq : (aℓ : a ⊏ ℓ) → Type
  Seq {ℓ} aℓ = Ord⁻ aℓ → Ord ℓ
  variable f g : Seq aℓ

  mono : (aℓ : a ⊏ ℓ) → Seq aℓ → Type
  mono aℓ f = ∀ {ν μ} → ν <⁻ μ → f ν <₁ f μ

  mono-prop : isProp (mono aℓ f)
  mono-prop {aℓ} {f} = isPropImplicitΠ2 λ _ _ → isProp→ squash₁
```

```agda
  module _ 
          {aℓᶠ : a ⊏ ℓ} {f : Ord⁻ aℓᶠ → Ord ℓ} {mᶠ : mono aℓᶠ f}
          {aℓᵍ : a ⊏ ℓ} {g : Ord⁻ aℓᵍ → Ord ℓ} {mᵍ : mono aℓᵍ g}
          (p : (ν : Ord⁻ aℓᶠ) → f ν ≡ g (♮ ν))
          where

    limExt : lim aℓᶠ f mᶠ ≡ lim aℓᵍ g mᵍ
    limExt with (pathToEq $ ⊏-prop aℓᶠ aℓᵍ)
    ... | rfl = cong₂ (O.A.lim aℓᶠ) (funExt λ ν → subst (λ x → f ν ≡ g x) ♭♯ (p ν)) (toPathP $ mono-prop _ _)
```

### 路径的良基性

```agda
  <-trans : Transitive (_<_ {ℓ})
  <-trans r zero = suc r
  <-trans r (suc s) = suc (<-trans r s)
  <-trans r (lim s) = lim (<-trans r s)

  <-acc : α < β → Acc _<_ α
  <-acc zero = acc λ s → <-acc s
  <-acc (suc r) = acc λ s → <-acc (<-trans s r)
  <-acc (lim r) = acc λ s → <-acc (<-trans s r)

  <-wf : WellFounded (_<_ {ℓ})
  <-wf _ = <-acc zero
```

```agda
  isPropAcc : isProp (Acc (_<₁_ {ℓ}) α)
  isPropAcc (acc p) (acc q) i = acc (λ r → isPropAcc (p r) (q r) i)

  <₁-acc : α <₁ β → Acc (_<₁_ {ℓ}) α
  <₁-acc ∣ zero  ∣₁ = acc λ r → <₁-acc r
  <₁-acc ∣ suc r ∣₁ = acc λ s → <₁-acc (map2 <-trans s ∣ r ∣₁)
  <₁-acc ∣ lim r ∣₁ = acc λ s → <₁-acc (map2 <-trans s ∣ r ∣₁)
  <₁-acc (squash₁ p q i) = isPropAcc (<₁-acc p) (<₁-acc q) i

  <₁-wf : WellFounded (_<₁_ {ℓ})
  <₁-wf _ = <₁-acc ∣ zero ∣₁
```

### 层级的提升

```agda
  lift : a ⊏ b → Ord a → Ord b
  lift-mono : {ab : a ⊏ b} {α β : Ord a} → α < β → lift ab α < lift ab β
```

```agda
  lift ab zero = zero
  lift ab (suc α) = suc (lift ab α)
  lift ab (lim {a = x} xa f mᶠ) = lim (⊏-trans xa ab)
    (λ ν → lift ab (f $ ♮ ν)) (map lift-mono ∘ mᶠ ∘ transport⁻ ♮-inj<)

  lift-mono zero = zero
  lift-mono (suc r) = suc (lift-mono r)
  lift-mono (lim {f} r) = lim (lift-mono $ subst⁻ (λ x → _ < f x) ♮-invo r)
```

```agda
open Hierarchy using (zero; suc; lim; lift; ♯) public
pattern one = suc zero
pattern ssuc x = suc (suc x)
```

## 层级族

```agda
unitLvStr : LevelStruct
unitLvStr = record
  { Lv = ⊤
  ; _⊏_ = λ _ _ → ⊥
  ; ⊏-wf = λ _ → acc λ ()
  ; ⊏-trans = λ ()
  ; ⊏-prop = isProp⊥ }
```

```agda
nextLvStr : (L : LevelStruct) (ℓ : LevelStruct.Lv L) → LevelStruct
nextLvStr L ℓ = record
  { Lv = Ord ℓ
  ; _⊏_ = _<₁_
  ; ⊏-wf = <₁-wf
  ; ⊏-trans = map2 <-trans
  ; ⊏-prop = squash₁ }
  where open Hierarchy {L}
```

```agda
LvStr : ℕ → LevelStruct

Lv : ℕ → Type
Lv k = LevelStruct.Lv (LvStr k)
variable k : ℕ; ℓ : Lv k

_⊏_ : Lv k → Lv k → Type; infix 6 _⊏_
_⊏_ {k} = LevelStruct._⊏_ (LvStr k)
```

```agda
iterΩ⁺ : ∀ k → Lv k

LvStr zero = unitLvStr
LvStr (suc k) = nextLvStr (LvStr k) (iterΩ⁺ k)
```

```agda
OrdStr : ∀ k → Lv k → OrderStruct
OrdStr k = Hierarchy.OrdStr {LvStr k}

Ord : Lv k → Type
Ord ℓ = OrdStr _ ℓ .fst

_<_ : {ℓ : Lv k} → Ord ℓ → Ord ℓ → Type; infix 6 _<_
_<_ {ℓ} = OrdStr _ ℓ .snd

_<₁_ : {ℓ : Lv k} → Ord ℓ → Ord ℓ → Type; infix 6 _<₁_
_<₁_ = Hierarchy._<₁_
```

```agda
OrdStr⁻ : {a ℓ : Lv k} → a ⊏ ℓ → OrderStruct
OrdStr⁻ {k} aℓ = Hierarchy.OrdStr⁻ {LvStr k} aℓ

Ord⁻ : {a ℓ : Lv k} → a ⊏ ℓ → Type
Ord⁻ aℓ = OrdStr⁻ aℓ .fst

_<⁻_ : {a ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type; infix 6 _<⁻_
_<⁻_ {aℓ} = OrdStr⁻ aℓ .snd
```

```agda
Ω : ∀ k (ℓ : Lv k) → Ord ℓ
Ω-mono-suc : {a : Lv (suc k)} {ν μ : Ord⁻ {suc k} {a} ∣ zero ∣₁}
  → ν <⁻ μ → lift ∣ zero ∣₁ (♯ ν) <₁ lift ∣ zero ∣₁ (♯ μ)

Ω zero ℓ = zero
Ω one zero = zero
Ω one (suc ℓ) = lim ∣ zero ∣₁ (λ ν → lift ∣ zero ∣₁ (♯ ν)) Ω-mono-suc
Ω (ssuc k) zero = zero
Ω (ssuc k) (suc ℓ) = lim ∣ zero ∣₁ (λ ν → lift ∣ zero ∣₁ (♯ ν)) Ω-mono-suc
Ω (ssuc k) (lim aℓ f mᶠ) = {!   !}

Ω-mono-suc = {!   !}
```

```agda
iterΩ⁺ zero = tt
iterΩ⁺ one = suc (Ω zero (iterΩ⁺ zero))
iterΩ⁺ (ssuc k) = suc (Ω (suc k) (iterΩ⁺ (suc k)))
```
