---
title: 形式化大数数学 (2.0 - 良构树序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.0 - 良构树序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/WellFormed.Base.html)  

## 基础的选取

立方类型论

```agda
{-# OPTIONS --safe --cubical #-}
module WellFormed.Base where
```

### 库依赖

cubical库

```agda
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Equality public using (pathToEq)
open import Cubical.Data.Empty public using (⊥; isProp⊥) renaming (elim to ⊥-elim)
open import Cubical.Data.Sigma public using (∃-syntax; _,_)
open import Cubical.Data.Sum public
  renaming (_⊎_ to infix 3 _⊎_) using (inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁) renaming (rec to rec₁)
```

标准库

```agda
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ public using ()
open import Function public using (id; _∘_; _$_; _∋_; it; case_of_)
open import Relation.Binary.PropositionalEquality public
  using () renaming (_≡_ to Eq; refl to reflEq)
```

## 良构树序数

互归纳定义良构树序数与子树关系.

```agda
data Ord : Type
Rel = Ord → Ord → Type
data _<_ : Rel; infix 4 _<_
```

```agda
_≤_ : Rel; infix 4 _≤_
a ≤ b = a < b ⊎ a ≡ b
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
  isProp< : isProp (a < b)
```

良构条件是命题

```agda
isPropWf : isProp (wf f)
isPropWf = isPropImplicitΠ (λ _ → isProp<)
```

极限的外延性

```agda
limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → f n ≡ g n) → lim f ≡ lim g
limExt {f} p = cong₂ (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
  (λ i n → p n i) (toPathP (isPropWf _ _))
```

## 树序数是集合

我们使用 [encode-decode 方法](https://ncatlab.org/nlab/show/encode-decode+method) 证明 $\text{Ord}$ 是同伦层级意义下的集合. 具体细节这里不展开, 大致分为以下四步:

1. 定义 `a b : Ord` 的覆叠空间 `Cover a b`, 容易证明它是一个命题.

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

isPropCover : ∀ a b → isProp (Cover a b)
isPropCover zero zero tt tt = refl
isPropCover (suc a) (suc b) = isPropCover a b
isPropCover (lim f) (lim g) = isPropΠ (λ n → isPropCover (f n) (g n))
```

2. 将 `a b : Ord` 的道路空间 `a ≡ b` 编码为覆叠空间.

```agda
encode : ∀ a b → a ≡ b → Cover a b
encode a b = J (λ b _ → Cover a b) (reflCode a)

encodeRefl : ∀ a → encode a a refl ≡ reflCode a
encodeRefl a = JRefl (λ b _ → Cover a b) (reflCode a)
```

3. 将覆叠空间解码为道路空间.

```agda
decode : ∀ a b → Cover a b → a ≡ b
decode zero zero _ = refl
decode (suc a) (suc b) p = cong suc (decode a b p)
decode (lim f) (lim g) p = limExt λ n → decode (f n) (g n) (p n)

decodeRefl : ∀ a → decode a a (reflCode a) ≡ refl
decodeRefl zero = refl
decodeRefl (suc a) i = cong suc (decodeRefl a i)
decodeRefl (lim f) i = cong₂
  (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
  (λ j n → decodeRefl (f n) i j)
  (isSet→SquareP {A = λ i j → wf (λ n → decodeRefl (f n) i j)}
    (λ _ _ → isProp→isSet isPropWf) (toPathP (isPropWf _ _)) refl refl refl i)
```

4. 证明编码与解码互逆, 结合 `Cover a b` 是命题, 说明 `Path a b` 是命题, 也即 `Ord` 是集合.

```agda
decodeEncode : ∀ a b p → decode a b (encode a b p) ≡ p
decodeEncode a _ = J (λ b p → decode a b (encode a b p) ≡ p)
  ((cong (decode a a) (encodeRefl a)) ∙ decodeRefl a)
  where open import Cubical.Foundations.Isomorphism

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

## 子树关系

```agda
<-trans : a < b → b < c → a < c
<-trans a<b <suc = <suc₂ a<b
<-trans a<f <lim = <lim₂ a<f
<-trans a<b (<suc₂ b<c) = <suc₂ (<-trans a<b b<c)
<-trans a<b (<lim₂ b<f) = <lim₂ (<-trans a<b b<f)
<-trans a<b (isProp< p q i) = isProp< (<-trans a<b p) (<-trans a<b q) i
```

```agda
lim-inv : ⦃ _ : wf f ⦄ → a < lim f → ∃[ n ∈ ℕ ] a < f n
lim-inv <lim   = ∣ _ , it ∣₁
lim-inv (<lim₂ a<f) = ∣ _ , a<f ∣₁
lim-inv (isProp< p q i) = squash₁ (lim-inv p) (lim-inv q) i
```

```agda
<-irrefl : a < b → a ≡ b → ⊥
<-irrefl p q = aux p (pathToEq q) where
  aux : a < b → Eq a b → ⊥
  aux {a = zero} (isProp< p q i) reflEq = isProp⊥ (aux p reflEq) (aux q reflEq) i
  aux {a = suc a} (<suc₂ p) reflEq = aux (<-trans <suc p) reflEq
  aux {a = suc a} (isProp< p q i) reflEq = isProp⊥ (aux p reflEq) (aux q reflEq) i
  aux {a = lim f} l<l reflEq = rec₁ isProp⊥ (λ { (n , p) → <-irrefl (<-trans <lim p) refl }) (lim-inv l<l)
```

```agda
isProp≤ : isProp (a ≤ b)
isProp≤ = isProp⊎ isProp< (isSetOrd _ _) <-irrefl
```

```agda
<s→≤ : a < suc b → a ≤ b
<s→≤ <suc = inr refl
<s→≤ (<suc₂ a<b) = inl a<b
<s→≤ (isProp< p q i) = isProp≤ (<s→≤ p) (<s→≤ q) i
```
