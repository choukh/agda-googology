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
  using (Σ-syntax; _×_; _,_; fst; snd; ΣPathP; PathPΣ)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map; map2; rec→Set)
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Function public using (id; flip; _∘_; _∘₂_; _$_; _∋_)
open import Relation.Binary.Definitions public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Induction.WellFounded as WF public
```

**桥接库**

用于处理Cubical库与标准库混用时的一些问题.

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Unit public using (⊤; tt; isProp⊤)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

**定义** 序结构

```agda
OrderStruct = Σ Type λ A → A → A → Type
```

## 层级

```agda
module Fix {Lv : Type} {_⊏_ : Lv → Lv → Type} (⊏-wf : WellFounded _⊏_) where
  private variable
    a ℓ ℓ′ : Lv
    aℓ : a ⊏ ℓ
```

### 定义的第1步: 互递归

```agda
  module O (ℓ : Lv) (O⁻ : ∀ {a} → a ⊏ ℓ → OrderStruct) where
    data U : Type
    data R : U → U → Type

    R₁ : U → U → Type
    R₁ α β = ∥ R α β ∥₁
```

```agda
    Seq : (aℓ : a ⊏ ℓ) → Type
    Seq aℓ = O⁻ aℓ .fst → U

    mono : Seq aℓ → Type
    mono {aℓ} f = Monotonic₁ (O⁻ aℓ .snd) R₁ f
```

```agda
    data U where
      zero : U
      suc : U → U
      lim : (aℓ : a ⊏ ℓ) (f : O⁻ aℓ .fst → U) (mᶠ : mono f) → U
```

```agda
    private variable α β : U
    data R where
      zero : R α (suc α)
      suc  : R α β → R α (suc β)
      lim  : {f : O⁻ aℓ .fst → U} {mᶠ : mono f} {ν : O⁻ aℓ .fst} → R α (f ν) → R α (lim aℓ f mᶠ)
```

```agda
  open O using (zero; suc; lim) public
```

### 定义的第2步: 强归纳

```agda
  module _ where
    open WF.All ⊏-wf

    OrdStr⁻ : a ⊏ ℓ → OrderStruct
    OrdStr⁻ = wfRecBuilder _ _ (λ ℓ o → O.U ℓ o , O.R ℓ o) _

    OrdStr : Lv → OrderStruct
    OrdStr = wfRec _ _ (λ ℓ o → O.U ℓ o , O.R ℓ o)
```

```agda
  Ord : Lv → Type
  Ord ℓ = OrdStr ℓ .fst
  private variable α β : Ord ℓ

  Road : Ord ℓ → Ord ℓ → Type
  Road = OrdStr _ .snd

  Road₁ : Ord ℓ → Ord ℓ → Type
  Road₁ = ∥_∥₁ ∘₂ Road
```

```agda
  Ord⁻ : a ⊏ ℓ → Type
  Ord⁻ aℓ = OrdStr⁻ aℓ .fst

  Road⁻ : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type
  Road⁻ {aℓ} = OrdStr⁻ aℓ .snd
```

### 表示变换

```agda
  opaque
    OrdStrFp : {aℓ : a ⊏ ℓ} → OrdStr⁻ aℓ ≡ OrdStr a
    OrdStrFp = FixPoint.wfRecBuilder-wfRec ⊏-wf _ _ (λ ℓ o → pathToEq $ ΣPathP $
      🧊.cong (O.U ℓ) (λ i aℓ → eqToPath (o aℓ) i) ,
      🧊.cong (O.R ℓ) (λ i aℓ → eqToPath (o aℓ) i)) _

    OrdFp : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ ≡ Ord a
    OrdFp = pathToEq $ fst $ PathPΣ $ eqToPath OrdStrFp
```

```agda
  ♯ : {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord a
  ♯ = subst id OrdFp

  ♭ : {aℓ : a ⊏ ℓ} → Ord a → Ord⁻ aℓ
  ♭ = subst id (sym OrdFp)

  ♮ : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} → Ord⁻ aℓ → Ord⁻ aℓ′
  ♮ = ♭ ∘ ♯
```

```agda
  open import Relation.Binary.PropositionalEquality using (subst-sym-subst; subst-subst-sym)
  ♭♯ : {aℓ : a ⊏ ℓ} {α : Ord⁻ aℓ} → ♭ (♯ α) ≡ α
  ♭♯ = subst-sym-subst OrdFp

  ♯♭ : {aℓ : a ⊏ ℓ} {α : Ord a} → ♯ {aℓ = aℓ} (♭ α) ≡ α
  ♯♭ = subst-subst-sym OrdFp
```

```agda
  Road♯Fp : {aℓ : a ⊏ ℓ} {α β : Ord⁻ aℓ} → Road⁻ α β ≡ Road (♯ α) (♯ β)
  Road♯Fp = {!   !}
```

### 基本性质

```agda
  Road-trans : Transitive (Road {ℓ})
  Road-trans r zero = suc r
  Road-trans r (suc s) = suc (Road-trans r s)
  Road-trans r (lim s) = lim (Road-trans r s)

  Road-acc : Road α β → Acc Road α
  Road-acc zero = acc λ s → Road-acc s
  Road-acc (suc r) = acc λ s → Road-acc (Road-trans s r)
  Road-acc (lim r) = acc λ s → Road-acc (Road-trans s r)

  Road-wf : WellFounded (Road {ℓ})
  Road-wf _ = Road-acc zero
```

```agda
  Seq : (aℓ : a ⊏ ℓ) → Type
  Seq {ℓ} aℓ = Ord⁻ aℓ → Ord ℓ

  mono : (aℓ : a ⊏ ℓ) → Seq aℓ → Type
  mono aℓ f = Monotonic₁ Road⁻ Road₁ f

  isPropMono : ∀ {f} → isProp (mono aℓ f)
  isPropMono {aℓ} {f} = isPropImplicitΠ2 λ _ _ → isProp→ squash₁
```

```agda
  limExtPath : {f g : Seq aℓ} {mᶠ : mono aℓ f} {mᵍ : mono aℓ g}
             → (∀ ν → f ν 🧊.≡ g ν) → lim aℓ f mᶠ 🧊.≡ lim aℓ g mᵍ
  limExtPath {aℓ} p = 🧊.cong₂ (λ f (mᶠ : mono aℓ f) → lim aℓ f mᶠ) (funExt p) (toPathP $ isPropMono _ _)

  limExt : {f g : Seq aℓ} {mᶠ : mono aℓ f} {mᵍ : mono aℓ g}
         → (∀ ν → f ν ≡ g ν) → lim aℓ f mᶠ ≡ lim aℓ g mᵍ
  limExt p = pathToEq $ limExtPath $ eqToPath ∘ p
```

```agda
open Fix using (zero; suc; lim) public
pattern one = suc zero
```

## 层级簇

```agda
Lv : ℕ → Type
Ord : ∀ {k} → Lv k → Type
```

```agda
variable
  k n m : ℕ
  a b ℓ ℓ′ : Lv k
  α β : Ord ℓ
```

```agda
Road : Ord ℓ → Ord ℓ → Type
Road-wf : WellFounded (Road {k} {ℓ})
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
Ord {suc k}    = Fix.Ord Road-wf

Road {(zero)}   = Fix.Road ⊤-wf
Road {suc k}    = Fix.Road Road-wf

Road-wf {(zero)}  = Fix.Road-wf ⊤-wf
Road-wf {suc k}   = Fix.Road-wf Road-wf
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
_⊏_ : ∀ {k} → Lv k → Lv k → Type
_⊏_ {(zero)} a b = ⊥
_⊏_ {suc k} = Road

⊏-wf : WellFounded (_⊏_ {k})
⊏-wf {(zero)} = ⊤-wf
⊏-wf {suc k} = Road-wf
```

```agda
Ord⁻ : {ℓ : Lv k} → a ⊏ ℓ → Type
Ord⁻ = Fix.Ord⁻ ⊏-wf

Road⁻ : {ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord⁻ aℓ → Ord⁻ aℓ → Type
Road⁻ = Fix.Road⁻ ⊏-wf
```

```agda
OrdFp : {ℓ : Lv k} {aℓ : a ⊏ ℓ} → Ord⁻ aℓ ≡ Ord a
OrdFp {suc k} = {! refl  !}
```

## 第零簇唯一层与自然数同构

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

## 层级的提升

```agda
mutual
  lift : a ⊏ b → Ord a → Ord b
  lift ab α = {!   !}

  lift-mono : {a b : Lv k} {ab : a ⊏ b} {α β : Ord a} → Monotonic₁ Road Road (lift ab)
  lift-mono = {!   !}
```
