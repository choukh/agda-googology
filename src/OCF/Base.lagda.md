---
title: 形式化大数数学 (3.0 - 高阶递归序数层级)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 高阶递归序数层级)

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
open import Cubical.Foundations.Prelude as 🧊 public
  hiding (Level; Lift; lift; _≡_; refl; sym; cong; cong₂; subst; _∎)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Equality using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
  using (Σ-syntax; _×_; _,_; fst; snd; ΣPathP)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map; map2; rec→Set)
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Product.Properties using (Σ-≡,≡→≡; Σ-≡,≡←≡)
open import Function public using (id; flip; _∘_; _$_; _∋_; case_of_)
open import Relation.Binary.Definitions public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong-app; subst; subst₂)
open import Relation.Binary.PropositionalEquality as Eq
open import Induction.WellFounded as WF public
```

**桥接库**

用于处理Cubical库与标准库混用时的一些问题.

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Unit public using (⊤; tt; isProp⊤)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

**定义** 转移

```agda
coe : {A B : Type} → A ≡ B → A → B
coe = subst id

coe⁻ : {A B : Type} → A ≡ B → B → A
coe⁻ = subst id ∘ sym
```

**定义** 序结构

```agda
OrderStruct = Σ Type λ A → A → A → Type
```

## 层级

```agda
module Fix {Lv : Type} {_⊏_ : Lv → Lv → Type} (⊏-wf : WellFounded _⊏_) where
  private variable
    a b ℓ ℓ′ : Lv
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

```agda
  Ord⁻ : a ⊏ ℓ → Type
  Ord⁻ aℓ = OrdStr⁻ aℓ .fst

  _<⁻_ : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type; infix 6 _<⁻_
  _<⁻_ {aℓ} = OrdStr⁻ aℓ .snd
```

### 表示变换

```agda
  OrdStrFp : {aℓ : a ⊏ ℓ} → OrdStr⁻ aℓ ≡ OrdStr a
  OrdStrFp = FixPoint.wfRecBuilder-wfRec ⊏-wf _ _ (λ ℓ o → pathToEq $ ΣPathP $
    🧊.cong (O.A ℓ) (λ i aℓ → eqToPath (o aℓ) i) ,
    🧊.cong (O.R ℓ) (λ i aℓ → eqToPath (o aℓ) i)) _

  OrdFp : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ ≡ Ord a
  OrdFp = Σ-≡,≡←≡ OrdStrFp .fst

  RoadFp : {aℓ : a ⊏ ℓ} → subst (λ A → A → A → Type) OrdFp (_<⁻_ {aℓ = aℓ}) ≡ _<_
  RoadFp = Σ-≡,≡←≡ OrdStrFp .snd
```

```agda
  ♯ : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord a
  ♯ = coe OrdFp

  ♭ : {aℓ : a ⊏ ℓ} → Ord a → Ord⁻ aℓ
  ♭ = coe⁻ OrdFp

  ♮ : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} → Ord⁻ aℓ → Ord⁻ aℓ′
  ♮ = ♭ ∘ ♯
```

```agda
  ♭♯ : {aℓ : a ⊏ ℓ} {α : Ord⁻ aℓ} → ♭ (♯ α) ≡ α
  ♭♯ = subst-sym-subst OrdFp

  ♯♭ : {aℓ : a ⊏ ℓ} {α : Ord a} → ♯ {aℓ = aℓ} (♭ α) ≡ α
  ♯♭ = subst-subst-sym OrdFp

  --♭(♯♭)♯ = ♭♯
  ♮♮ : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α : Ord⁻ aℓ} → ♮ {aℓ = aℓ′} (♮ α) ≡ α
  ♮♮ = trans (cong ♭ (trans ♯♭ (cong ♯ refl))) ♭♯
```

```agda
  <-distrib-subst : {aℓ : a ⊏ ℓ} → (λ α β → ♭ {aℓ = aℓ} α <⁻ ♭ β) ≡ subst (λ A → A → A → Type) OrdFp (_<⁻_ {aℓ = aℓ})
  <-distrib-subst = Eq.J (λ _ eq → (λ α β → coe⁻ eq α <⁻ coe⁻ eq β) ≡ subst _ eq _<⁻_) OrdFp refl

  ♭<⁻♭≡< : {aℓ : a ⊏ ℓ} {α β : Ord a} → ♭ {aℓ = aℓ} α <⁻ ♭ β ≡ α < β
  ♭<⁻♭≡< = cong-app (cong-app (trans <-distrib-subst RoadFp) _) _

  ♯<♯≡<⁻ : {aℓ : a ⊏ ℓ} {α β : Ord⁻ aℓ} → ♯ α < ♯ β ≡ α <⁻ β
  ♯<♯≡<⁻ = subst₂ (λ x y → ♯ _ < ♯ _ ≡ x <⁻ y) ♭♯ ♭♯ (sym ♭<⁻♭≡<)

  ♮<⁻♮≡<⁻ : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α β : Ord⁻ aℓ} → ♮ {aℓ′ = aℓ′} α <⁻ ♮ β ≡ α <⁻ β
  ♮<⁻♮≡<⁻ = trans ♭<⁻♭≡< ♯<♯≡<⁻
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

```agda
open Fix using (zero; suc; lim) public
pattern one = suc zero
pattern ssuc x = suc (suc x)
```

## 层级簇

```agda
Lv : ℕ → Type
Ord : ∀ {k} → Lv k → Type
```

```agda
variable
  k n m : ℕ
  a b c ℓ ℓ′ : Lv k
  α β : Ord ℓ
```

```agda
_<_ : Ord ℓ → Ord ℓ → Type; infix 6 _<_

_<₁_ : Ord ℓ → Ord ℓ → Type; infix 6 _<₁_
α <₁ β = ∥ α < β ∥₁

<₁-wf : WellFounded (_<₁_ {k} {ℓ})
```

```agda
finLv  : ℕ → Lv k
finOrd : ℕ → Ord ℓ

open import Agda.Builtin.FromNat public
instance
  nNat : Number ℕ
  nNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nLv : Number (Lv k)
  nLv = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finLv n }
  nOrd : Number (Ord ℓ)
  nOrd = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finOrd n }
```

```agda
Lv zero    = ⊤
Lv (suc k) = Ord {k} 1

⊤-wf : WellFounded (λ (_ _ : ⊤) → ⊥)
⊤-wf _ = acc λ ()

Ord {(zero)}   = Fix.Ord ⊤-wf
Ord {suc k}    = Fix.Ord <₁-wf

_<_ {(zero)}   = Fix._<_ ⊤-wf
_<_ {suc k}    = Fix._<_ <₁-wf

<₁-wf {(zero)}  = Fix.<₁-wf ⊤-wf
<₁-wf {suc k}   = Fix.<₁-wf <₁-wf
```

```agda
finLv k@{zero}        _       = tt
finLv k@{one}         zero    = zero
finLv k@{one}         (suc n) = suc (finLv {k} n)
finLv k@{suc (suc _)} zero    = zero
finLv k@{suc (suc _)} (suc n) = suc (finLv {k} n)
```

```agda
finOrd k@{zero}  zero    = zero
finOrd k@{zero}  (suc n) = suc (finOrd {k} n)
finOrd k@{suc _} zero    = zero
finOrd k@{suc _} (suc n) = suc (finOrd {k} n)
```

### 表示变换

```agda
_⊏_ : ∀ {k} → Lv k → Lv k → Type; infix 6 _⊏_
_⊏_ {(zero)} a b = ⊥
_⊏_ {suc k} = _<₁_
variable aℓ : a ⊏ ℓ

⊏-wf : WellFounded (_⊏_ {k})
⊏-wf {(zero)} = ⊤-wf
⊏-wf {suc k} = <₁-wf
```

```agda
Ord⁻ : {a ℓ : Lv k} → a ⊏ ℓ → Type
Ord⁻ = Fix.Ord⁻ ⊏-wf

_<⁻_ : {a ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type; infix 6 _<⁻_
_<⁻_ = Fix._<⁻_ ⊏-wf
```

```agda
♯ : {a ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord a
♯ {suc k} = Fix.♯ ⊏-wf

♭ : {a ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord a → Ord⁻ aℓ
♭ {suc k} = Fix.♭ ⊏-wf

♮ : {a ℓ ℓ′ : Lv k} {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} → Ord⁻ aℓ → Ord⁻ aℓ′
♮ {suc k} = Fix.♮ ⊏-wf

♮♮ : {a ℓ ℓ′ : Lv k} {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α : Ord⁻ aℓ} → ♮ {aℓ = aℓ′} (♮ α) ≡ α
♮♮ {suc k} = Fix.♮♮ ⊏-wf

♮<⁻♮≡<⁻ : {a ℓ ℓ′ : Lv k} {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} {α β : Ord⁻ aℓ} → ♮ {aℓ′ = aℓ′} α <⁻ ♮ β ≡ α <⁻ β
♮<⁻♮≡<⁻ {suc k} = Fix.♮<⁻♮≡<⁻ ⊏-wf
```

### 极限的外延性

```agda
Seq : {a ℓ : Lv k} (aℓ : a ⊏ ℓ) → Type
Seq {ℓ} aℓ = Ord⁻ aℓ → Ord ℓ
variable f g : Seq aℓ

mono : {a ℓ : Lv k} (aℓ : a ⊏ ℓ) → Seq aℓ → Type
mono aℓ f = ∀ {ν μ} → ν <⁻ μ → f ν <₁ f μ

isPropMono : isProp (mono aℓ f)
isPropMono {aℓ} {f} = isPropImplicitΠ2 λ _ _ → isProp→ squash₁
```

```agda
module _ {a ℓ : Lv (suc k)}
         {aℓᶠ : a ⊏ ℓ} {f : Ord⁻ aℓᶠ → Ord ℓ} {mᶠ : mono aℓᶠ f}
         {aℓᵍ : a ⊏ ℓ} {g : Ord⁻ aℓᵍ → Ord ℓ} {mᵍ : mono aℓᵍ g}
         (p : {aℓ : a ⊏ ℓ} (ν : Ord⁻ aℓ) → f (♮ {aℓ′ = aℓᶠ} ν) ≡ g (♮ {aℓ′ = aℓᵍ} ν))
         where

  limExtPath : lim aℓᶠ f mᶠ 🧊.≡ lim aℓᵍ g mᵍ
  limExtPath i = lim (squash₁ aℓᶠ aℓᵍ i)
    (λ (ν : Ord⁻ (squash₁ aℓᶠ aℓᵍ i)) → {! eqToPath (p ν) i  !})
    {!   !}

  limExt : lim aℓᶠ f mᶠ ≡ lim aℓᵍ g mᵍ
  limExt = pathToEq limExtPath
```

### 零簇唯一层与自然数同构

```agda
module OrdZeroIso where
  Ord₀ = Ord {zero} tt

  to : Ord₀ → ℕ
  to zero = zero
  to (suc n) = suc (to n)

  from : ℕ → Ord₀
  from zero = zero
  from (suc n) = suc (from n)

  to-from : ∀ n → to (from n) 🧊.≡ n
  to-from zero = 🧊.refl
  to-from (suc n) = 🧊.cong suc (to-from n)

  from-to : ∀ α → from (to α) 🧊.≡ α
  from-to zero = 🧊.refl
  from-to (suc n) = 🧊.cong suc (from-to n)

  Ord₀≅ℕ : Iso Ord₀ ℕ
  Ord₀≅ℕ = iso to from to-from from-to

  Ord₀≡ℕ : Ord₀ ≡ ℕ
  Ord₀≡ℕ = pathToEq $ isoToPath Ord₀≅ℕ
```

## 路径关系

```agda
<-trans : Transitive (_<_ {k} {ℓ})
<-trans {(zero)} = Fix.<-trans ⊤-wf
<-trans {suc k} = Fix.<-trans ⊏-wf
```

## 层级的提升

```agda
lift : {a b : Lv (suc k)} → a ⊏ b → Ord a → Ord b
lift-mono : {a b : Lv (suc k)} {ab : a ⊏ b} {α β : Ord a} → α < β → _<_ {suc k} (lift ab α) (lift ab β)

lift ab zero = zero
lift ab (suc α) = suc (lift ab α)
lift ab (lim xa f mᶠ) = lim (map2 <-trans xa ab) (λ ν → lift ab (f $ ♮ ν)) (map lift-mono ∘ mᶠ ∘ coe⁻ ♮<⁻♮≡<⁻)

lift-mono zero = zero
lift-mono (suc r) = suc (lift-mono r)
lift-mono (lim {f} r) = lim (lift-mono $ subst (λ x → _ < f x) (sym ♮♮) r)
```

提升的复合

```agda
lift-comp : {a b : Lv (suc k)} {ab : a ⊏ b} {bc : b ⊏ c} {ac : a ⊏ c} {α : Ord a} → lift ac α ≡ lift bc (lift ab α)
lift-comp {α = zero} = refl
lift-comp {α = suc α} = cong suc lift-comp
lift-comp {ab} {bc} {ac} {α = lim _ f _} = {!   !}
  --limExt (λ ν → subst₂ (λ x y → lift ac (f x) ≡ lift bc (lift ab (f y)))
  --{!  ν !} {!   !} lift-comp)
```
