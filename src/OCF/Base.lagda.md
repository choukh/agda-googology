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
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Foundations.Isomorphism public
  using (Iso; iso; isoToPath)
open import Cubical.Data.Sigma public
  using (Σ-syntax; _×_; _,_; fst; snd; ΣPathP)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map; map2; rec→Set)
```

**标准库**

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Function public using (id; flip; _∘_; _$_)
open import Relation.Binary.Definitions public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Induction.WellFounded as WF public
open WF.All using (wfRec)
```

**桥接库**

用于处理Cubical库与标准库混用时的一些问题.

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Unit public using (⊤; tt; isProp⊤)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

## 高阶递归序数层级

```agda
OrderStruct = Σ Type λ A → A → A → Type
```

```agda
module Fix {Lv : Type} {_⊏_ : Lv → Lv → Type} (⊏-wf : WellFounded _⊏_) where
  private variable
    a ℓ : Lv
    al : a ⊏ ℓ
```

```agda
  module O (ℓ : Lv) (O⁻ : ∀ {a} → a ⊏ ℓ → OrderStruct) where
    data U : Type
    data R : U → U → Type
```

```agda
    R₁ : U → U → Type
    R₁ α β = ∥ R α β ∥₁
```

```agda
    mono : (O⁻ al .fst → U) → Type
    mono {al} f = Monotonic₁ (O⁻ al .snd) R₁ f
```

```agda
    data U where
      zero : U
      suc : U → U
      lim : (al : a ⊏ ℓ) (f : O⁻ al .fst → U) (mᶠ : mono f) → U
```

```agda
    private variable α β : U
    data R where
      zero : R α (suc α)
      suc  : R α β → R α (suc β)
      lim  : {f : O⁻ al .fst → U} {mᶠ : mono f} {ν : O⁻ al .fst} → R α (f ν) → R α (lim al f mᶠ)
```

```agda
  open O using (zero; suc; lim) public
```

```agda
  OrdStr : Lv → OrderStruct
  OrdStr = wfRec ⊏-wf _ _ λ ℓ u⁻ → O.U ℓ u⁻ , O.R ℓ u⁻

  Ord : Lv → Type
  Ord ℓ = OrdStr ℓ .fst
  private variable α β : Ord ℓ

  Road : Ord ℓ → Ord ℓ → Type
  Road = OrdStr _ .snd
```

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
open Fix using (zero; suc; lim) public
```

## 层级的迭代

```agda
Lv : ℕ → Type
OrdStr : ∀ k → Lv k → OrderStruct

Ord : ∀ k → Lv k → Type
Ord k ℓ = OrdStr k ℓ .fst
```

```agda
variable
  k n m : ℕ
  a b ℓ ℓ′ : Lv k
  α β : Ord k ℓ
```

```agda
Road : Ord _ ℓ → Ord _ ℓ → Type
Road {ℓ} = OrdStr _ ℓ .snd

Road-wf : WellFounded (Road {k} {ℓ})
```

```agda
finLv : ℕ → Lv k
finOrd : {ℓ : Lv k} → ℕ → Ord _ ℓ

open import Agda.Builtin.FromNat public
instance
  nNat : Number ℕ
  nNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nLv : Number (Lv k)
  nLv = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finLv n }
  nOrd : Number (Ord k ℓ)
  nOrd = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finOrd n }
```

```agda
Lv zero    = ⊤
Lv (suc k) = OrdStr k 1 .fst

⊤-wf : WellFounded (λ (_ _ : ⊤) → ⊥)
⊤-wf _ = acc λ ()

OrdStr zero    = Fix.OrdStr ⊤-wf
OrdStr (suc k) = Fix.OrdStr Road-wf

Road-wf {(zero)} = Fix.Road-wf ⊤-wf
Road-wf {suc k}  = Fix.Road-wf Road-wf
```

```agda
finLv k@{zero}        _       = tt
finLv k@{suc zero}    zero    = zero
finLv k@{suc zero}    (suc n) = suc (finLv {k} n)
finLv k@{suc (suc _)} zero    = zero
finLv k@{suc (suc _)} (suc n) = suc (finLv {k} n)
```

```agda
finOrd k@{zero}  zero    = zero
finOrd k@{zero}  (suc n) = suc (finOrd {k} n)
finOrd k@{suc _} zero    = zero
finOrd k@{suc _} (suc n) = suc (finOrd {k} n)
```

```agda
module OrdZeroIso where
  to : Ord zero tt → ℕ
  to zero = zero
  to (suc n) = suc (to n)

  from : ℕ → Ord zero tt
  from zero = zero
  from (suc n) = suc (from n)

  to-from : ∀ n → to (from n) 🧊.≡ n
  to-from zero = 🧊.refl
  to-from (suc n) = 🧊.cong suc (to-from n)

  from-to : ∀ α → from (to α) 🧊.≡ α
  from-to zero = 🧊.refl
  from-to (suc n) = 🧊.cong suc (from-to n)

  Ord₀≅ℕ : Iso (Ord zero tt) ℕ
  Ord₀≅ℕ = iso to from to-from from-to

  Ord₀≡ℕ : Ord zero tt ≡ ℕ
  Ord₀≡ℕ = pathToEq $ isoToPath Ord₀≅ℕ
```
