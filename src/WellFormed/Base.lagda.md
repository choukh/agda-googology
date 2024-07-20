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
open import Function public using (id; _∘_; _$_; _∋_; it)
open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality public hiding ([_])
```

```agda
open import Relation.Binary hiding (Rel)
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded using (Acc; acc; WellFounded)
```

```agda
open import Cubical.Foundations.Prelude public using (Type)
open import Cubical.Data.Equality public using (funExt)
open import Cubical.HITs.PropositionalTruncation public using (∥_∥₁)
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
  as SubTreeLe public using (_≤_; <⇒≤)
```

**定义** 序数的严格单调递增序列

```agda
Seq : Set
Seq = ℕ → Ord

wf : Seq → Type
wf f = ∀ {n} → ∥ f n < f (suc n) ∥₁
```

```agda
variable
  m n : ℕ
  f g h : Seq
  a b c d i : Ord
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
  <lim  : ∀ f n → ⦃ _ : wf f ⦄ → f n < lim f
  <lim₂ : ∀ f n → ⦃ _ : wf f ⦄ → a < f n → a < lim f
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

**约定** 非零序数指不等于零的序数, 非平凡序数指不等于零或一的序数.

```agda
not0 : Ord → Set
not0 zero = ⊥
not0 _ = ⊤

record NonZero (a : Ord) : Set where
  field nonZero : not0 a
```

```agda
nz-intro : 0 < a → NonZero a
nz-intro {suc _} _ = _
nz-intro {lim _} _ = _
```

## 基本性质

构造子的单射性

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

极限的外延性

```agda
limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → f n ≡ g n) → lim f ≡ lim g
limExt {f} p with funExt p
... | refl = cong (λ (p : wf f) → lim f ⦃ p ⦄) {!   !}
```

良构性恢复为路径集

```agda
per : (f : Seq) → ⦃ ∀ {n} → ∥ f n < f (suc n) ∥₁ ⦄ → f n < f (suc n)
per f = {!   !}
```

严格序与非严格序的相互转化

```agda
≤→<s : a ≤ b → a < suc b
≤→<s (inj₁ p) = <suc₂ p
≤→<s (inj₂ refl) = <suc

<s→≤ : a < suc b → a ≤ b
<s→≤ <suc = inj₂ refl
<s→≤ (<suc₂ p) = inj₁ p
```

互递归证明

```agda
z<s : 0 < suc a
z<b : a < b → 0 < b

z<s {(zero)}  = <suc
z<s {suc a}   = <suc₂ z<s
z<s {lim f}   = <suc₂ $ <lim₂ f 1 $ z<b (per f)

z<b <suc = z<s
z<b (<suc₂ p) = z<s
z<b (<lim f n) = <lim₂ f (suc n) $ z<b (per f)
z<b (<lim₂ f n p) = <lim₂ f 1 $ z<b (per f)
```
