---
title: 形式化大数数学 (2.0 - 良构树序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.0 - 良构树序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/WellFormed.Base.html)  

## 前言

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Base where
```

### 标准库依赖

```agda
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ public using ()
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Product public using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Function public using (id; _∘_; _$_; _∋_; it; case_of_; _↪_)
open import Relation.Nullary public using (¬_)
open import Relation.Binary public hiding (Rel)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl)

open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded using (Acc; acc; WellFounded)
```

立方类型论

```agda
open import Cubical.Foundations.Prelude as 🧊 public
  renaming (_≡_ to Path)
  using (Type; isProp; isProp→PathP)
open import Cubical.Foundations.HLevels public
  using (isPropImplicitΠ)
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath)
```

函数外延性

```agda
funExt : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : (x : A) → B x}
  → ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToEq (λ i x → eqToPath (p x) i)

implicitFunExt : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : {x : A} → B x}
  → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
implicitFunExt p = pathToEq (λ i {x} → eqToPath (p x) i)
```

## 良构树序数

互归纳定义良构树序数与子树关系.

```agda
data Ord : Type
Rel = Ord → Ord → Type
data _<_ : Rel; infix 4 _<_
```

```agda
_≮_ : Rel; infix 4 _≮_
a ≮ b = ¬ a < b
```

```agda
open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as SubTreeLe public using (_≤_) renaming (<⇒≤ to <→≤)
```

**定义** 严格单调递增序列

```agda
Seq : Type
Seq = ℕ → Ord

wf : Seq → Type
wf f = ∀ {n} → f n < f (suc n)
```

```agda
variable
  m n : ℕ
  a b c d i : Ord
  f g h : Seq
```

**定义** 良构树序数

```agda
data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : (f : Seq) → ⦃ wf f ⦄ → Ord
```

**定义** 子树关系

```agda
data _<_ where
  <suc  : a < suc a
  <suc₂ : a < b → a < suc b
  <lim  : ⦃ _ : wf f ⦄ → f n < lim f
  <lim₂ : ⦃ _ : wf f ⦄ → a < f n → a < lim f
  <prop : isProp (a < b)
```

**定义** 自然数到序数的嵌入 $\text{fin} : ℕ → \text{Ord}$

$$
\text{fin}~n := \text{suc}^n~0
$$

其中后继函数的上标 $n$ 表示迭代 $n$ 次.

```agda
open import Lower public using (_∘ⁿ_)
fin : Seq
fin n = (suc ∘ⁿ n) zero
```

**约定** 数字字面量既可以表示自然数, 也可以表示序数. Agda 使用[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能实现该约定.

```agda
open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }
```

**约定** 我们将 $\text{suc}~(\text{suc}~a)$ 记作 $a^{++}$.

```agda
pattern 2+ a = suc (suc a)
```

## 集合性

encode-decode

```agda
Cover : Ord → Ord → Type
Cover zero    zero    = ⊤
Cover zero    (suc b) = ⊥
Cover zero    (lim f) = ⊥
Cover (suc a) zero    = ⊥
Cover (suc a) (suc b) = Path a b
Cover (suc a) (lim f) = ⊥
Cover (lim f) zero    = ⊥
Cover (lim f) (suc b) = ⊥
Cover (lim f) (lim g) = Path f g
```

```agda
reflCode : (a : Ord) → Cover a a
reflCode zero = tt
reflCode (suc a) = 🧊.refl
reflCode (lim f) = 🧊.refl
```

```agda
encode : ∀ a b → Path a b → Cover a b
encode a b = 🧊.J (λ b _ → Cover a b) (reflCode a)

encodeRefl : ∀ a → Path (encode a a 🧊.refl) (reflCode a)
encodeRefl a = 🧊.JRefl (λ b _ → Cover a b) (reflCode a)
```

```agda
decode : ∀ a b → Cover a b → Path a b
decode zero zero p = 🧊.refl
decode (suc a) (suc b) p = 🧊.cong suc p
decode (lim f) (lim g) p = 🧊.cong₂ (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄) p
  (isProp→PathP (λ _ → isPropImplicitΠ (λ _ → <prop)) it it)

decodeRefl : ∀ a → Path (decode a a (reflCode a)) 🧊.refl
decodeRefl zero = 🧊.refl
decodeRefl (suc a) = 🧊.refl
decodeRefl (lim f) i = 🧊.cong (λ (wff : wf f) → lim f ⦃ wff ⦄)
  {!   !}
```
