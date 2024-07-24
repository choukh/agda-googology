---
title: 形式化大数数学 (2.0 - 良构树序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.0 - 良构树序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/WellFormed.Base.html)  

## 基础的选取

```agda
{-# OPTIONS --safe --cubical #-}
module WellFormed.Base where
```

### 标准库依赖

```agda
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Product public using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Function public using (id; _∘_; _$_; _∋_; it; case_of_; _↪_)
open import Relation.Nullary public using (¬_)
open import Relation.Binary public hiding (Rel)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl)

open import Data.Nat.Properties as ℕ using ()
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded using (Acc; acc; WellFounded)
```

立方类型论

```agda
open import Cubical.Foundations.Prelude as 🧊
  using (Type; isProp; isSet; toPathP; isProp→isSet) renaming (_≡_ to Path)
open import Cubical.Foundations.HLevels
  using (isPropΠ; isPropImplicitΠ; isOfHLevelRetract; isSet→SquareP)
open import Cubical.Foundations.Isomorphism using (isoToPath; iso)
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
  lim  : (f : Seq) → ⦃ wff : wf f ⦄ → Ord
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

良构条件是命题

```agda
wf-prop : isProp (wf f)
wf-prop = isPropImplicitΠ (λ _ → <prop)
```

极限的外延性

```agda
limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → f n 🧊.≡ g n) → lim f 🧊.≡ lim g
limExt {f} p = 🧊.cong₂ (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
  (λ i n → p n i) (toPathP (wf-prop _ _))
```

## 树序数是集合

使用 [encode-decode 方法](https://ncatlab.org/nlab/show/encode-decode+method) 可以证明 $\text{Ord}$ 是同伦层级意义下的集合.

```agda
Cover : Ord → Ord → Type
Cover zero    zero    = ⊤
Cover (suc a) (suc b) = Cover a b
Cover (lim f) (lim g) = ∀ n → Cover (f n) (g n)
Cover _       _       = ⊥

reflCode : (a : Ord) → Cover a a
reflCode zero = tt
reflCode (suc a) = reflCode a
reflCode (lim f) n = reflCode (f n)
```

```agda
encode : ∀ a b → Path a b → Cover a b
encode a b = 🧊.J (λ b _ → Cover a b) (reflCode a)

encodeRefl : ∀ a → Path (encode a a 🧊.refl) (reflCode a)
encodeRefl a = 🧊.JRefl (λ b _ → Cover a b) (reflCode a)
```

```agda
decode : ∀ a b → Cover a b → Path a b
decode zero zero _ = 🧊.refl
decode (suc a) (suc b) p = 🧊.cong suc (decode a b p)
decode (lim f) (lim g) p = limExt λ n → decode (f n) (g n) (p n)

decodeRefl : ∀ a → Path (decode a a (reflCode a)) 🧊.refl
decodeRefl zero = 🧊.refl
decodeRefl (suc a) i = 🧊.cong suc (decodeRefl a i)
decodeRefl (lim f) i = 🧊.cong₂
  (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
  (λ j n → decodeRefl (f n) i j)
  (isSet→SquareP {A = λ i j → wf (λ n → decodeRefl (f n) i j)}
    (λ _ _ → isProp→isSet wf-prop) (toPathP (wf-prop _ _)) 🧊.refl 🧊.refl 🧊.refl i)
```

```agda
decodeEncode : ∀ a b p → Path (decode a b (encode a b p)) p
decodeEncode a _ = 🧊.J (λ b p → Path (decode a b (encode a b p)) p)
  ((🧊.cong (decode a a) (encodeRefl a)) 🧊.∙ decodeRefl a)

isPropCover : ∀ a b → isProp (Cover a b)
isPropCover zero zero tt tt = 🧊.refl
isPropCover (suc a) (suc b) = isPropCover a b
isPropCover (lim f) (lim g) = isPropΠ (λ n → isPropCover (f n) (g n))

isSetOrd : isSet Ord
isSetOrd a b = isOfHLevelRetract 1 (encode a b) (decode a b) (decodeEncode a b) (isPropCover a b)
```

## 一些约定

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

## 基本性质
