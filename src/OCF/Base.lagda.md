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
open import Cubical.Foundations.Prelude public
  hiding (Level; Lift; lift; _≡_; refl; sym; cong; cong₂; subst; _∎)
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

## 自然数

```agda
variable k n m : ℕ

data _<ᴺ_ : ℕ → ℕ → Type where
  zero : n <ᴺ suc n
  suc  : n <ᴺ m → n <ᴺ suc m

<ᴺ-trans : Transitive _<ᴺ_
<ᴺ-trans r zero = suc r
<ᴺ-trans r (suc s) = suc (<ᴺ-trans r s)

<ᴺ-acc : n <ᴺ m → Acc _<ᴺ_ n
<ᴺ-acc zero = acc λ s → <ᴺ-acc s
<ᴺ-acc (suc r) = acc (λ s → <ᴺ-acc (<ᴺ-trans s r))

<ᴺ-wf : WellFounded _<ᴺ_
<ᴺ-wf _ = <ᴺ-acc zero
```

## 高阶递归序数层级

```agda
OrderStruct = Σ Type λ A → A → A → Type
```

```agda
module Fix (Lv : Type) (_⊏_ : Lv → Lv → Type) (⊏-wf : WellFounded _⊏_) where
  private variable
    a l : Lv
    al : a ⊏ l
```

```agda
  module O (l : Lv) (O⁻ : ∀ {a} → a ⊏ l → OrderStruct) where
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
      lim : (al : a ⊏ l) (f : O⁻ al .fst → U) (mᶠ : mono f) → U
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
  OrdStr = wfRec ⊏-wf _ _ λ l u⁻ → O.U l u⁻ , O.R l u⁻

  Ord : Lv → Type
  Ord l = OrdStr l .fst
  private variable α β : Ord l

  Road : Ord l → Ord l → Type
  Road = OrdStr _ .snd
```

```agda
  Road-trans : Transitive (Road {l})
  Road-trans r zero = suc r
  Road-trans r (suc s) = suc (Road-trans r s)
  Road-trans r (lim s) = lim (Road-trans r s)

  Road-acc : Road α β → Acc Road α
  Road-acc zero = acc λ s → Road-acc s
  Road-acc (suc r) = acc λ s → Road-acc (Road-trans s r)
  Road-acc (lim r) = acc λ s → Road-acc (Road-trans s r)

  Road-wf : WellFounded (Road {l})
  Road-wf _ = Road-acc zero
```

```agda
open Fix using (zero; suc; lim) public
```

```agda
Lv : ℕ → Type
OrdStr : ∀ k → Lv k → OrderStruct
variable a b l l′ : Lv k
```

```agda
Ord : ∀ k → Lv k → Type
Ord k l = OrdStr k l .fst

Road : Ord _ l → Ord _ l → Type
Road {l} = OrdStr _ l .snd

Road-wf : WellFounded (Road {k} {l})
```

```agda
finLv : ℕ → Lv k
finOrd : {l : Lv k} → ℕ → Ord _ l

open import Agda.Builtin.FromNat public
instance
  nNat : Number ℕ
  nNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nLv : Number (Lv n)
  nLv = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finLv n }
  nOrd : Number (Ord _ l)
  nOrd = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finOrd n }
```

```agda
Lv zero     = ℕ
Lv (suc k)  = OrdStr k 1 .fst

OrdStr zero    = Fix.OrdStr _ _ <ᴺ-wf
OrdStr (suc k) = Fix.OrdStr _ _ Road-wf

Road-wf {(zero)} {l} = Fix.Road-wf _ _ <ᴺ-wf
Road-wf {suc k}  {l} = Fix.Road-wf _ _ Road-wf
```

```agda
finLv k@{(zero)}              = id
finLv k@{suc zero}    zero    = zero
finLv k@{suc zero}    (suc n) = suc (finLv {k} n)
finLv k@{suc (suc _)} zero    = zero
finLv k@{suc (suc _)} (suc n) = suc (finLv {k} n)
```

```agda
finOrd k@{(zero)} zero      = zero
finOrd k@{(zero)} (suc n)   = suc (finOrd {k} n)
finOrd {k@(suc _)} zero     = zero
finOrd {k@(suc _)} (suc n)  = suc (finOrd {k} n)
```
