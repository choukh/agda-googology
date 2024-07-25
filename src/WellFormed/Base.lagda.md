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
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Base where
```

### 库依赖

cubical库

```agda
open import Cubical.Foundations.Prelude as 🧊 public
  using (Type; toPathP; isProp; isSet; isProp→isSet)
  renaming (_≡_ to Path; refl to reflPath)
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Equality public using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
  using (Σ; Σ-syntax; ∃-syntax; _×_; fst; snd; _,_; ΣPathP)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; map; map2)
```

标准库

```agda
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Function public using (id; flip; _∘_; _$_; _∋_; it; case_of_)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; subst)
```

融合库

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

## 良构树序数

互归纳定义良构树序数与路径集.

```agda
data Ord : Type
Rel = Ord → Ord → Type
data Route : Rel
```

路径集的截断叫做子树关系.

```agda
_<_ : Rel; infix 6 _<_
a < b = ∥ Route a b ∥₁

open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as SubTreeLe public using () renaming (_≤_ to infix 6 _≤_; <⇒≤ to <→≤)
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

**定义** 路径集

```agda
data Route where
  suc  : Route a (suc a)
  suc₂ : Route a b → Route a (suc b)
  lim  : ⦃ _ : wf f ⦄ → Route (f n) (lim f)
  lim₂ : ⦃ _ : wf f ⦄ → Route a (f n) → Route a (lim f)
```

### 基本性质

构造子的单射性

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

良构条件是命题

```agda
isPropWf : isProp (wf f)
isPropWf = isPropImplicitΠ λ _ → squash₁
```

极限的外延性

```agda
limExtPath : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → Path (f n) (g n)) → Path (lim f) (lim g)
limExtPath {f} p = 🧊.cong₂ (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
  (λ i n → p n i) (toPathP (isPropWf _ _))

limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → f n ≡ g n) → lim f ≡ lim g
limExt p = pathToEq $ limExtPath $ eqToPath ∘ p
```

### 一些约定

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

## 树序数是集合

```agda
module OrdSet where
  open import Cubical.Foundations.Isomorphism
```

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
  isPropCover zero zero tt tt = reflPath
  isPropCover (suc a) (suc b) = isPropCover a b
  isPropCover (lim f) (lim g) = isPropΠ (λ n → isPropCover (f n) (g n))
```

2. 将 `a b : Ord` 的道路空间 `Path a b` 编码为覆叠空间.

```agda
  encode : ∀ a b → Path a b → Cover a b
  encode a b = 🧊.J (λ b _ → Cover a b) (reflCode a)

  encodeRefl : ∀ a → Path (encode a a reflPath) (reflCode a)
  encodeRefl a = 🧊.JRefl (λ b _ → Cover a b) (reflCode a)
```

3. 将覆叠空间解码为道路空间.

```agda
  decode : ∀ a b → Cover a b → Path a b
  decode zero zero _ = reflPath
  decode (suc a) (suc b) p = 🧊.cong suc (decode a b p)
  decode (lim f) (lim g) p = limExtPath λ n → decode (f n) (g n) (p n)

  decodeRefl : ∀ a → Path (decode a a (reflCode a)) reflPath
  decodeRefl zero = reflPath
  decodeRefl (suc a) i = 🧊.cong suc (decodeRefl a i)
  decodeRefl (lim f) i = 🧊.cong₂
    (λ (f : Seq) (wff : wf f) → lim f ⦃ wff ⦄)
    (λ j n → decodeRefl (f n) i j)
    (isSet→SquareP {A = λ i j → wf (λ n → decodeRefl (f n) i j)}
      (λ _ _ → isProp→isSet isPropWf) (toPathP (isPropWf _ _)) reflPath reflPath reflPath i)
```

4. 证明编码与解码互逆, 结合 `Cover a b` 是命题, 说明 `Path a b` 是命题, 也即 `Ord` 是集合.

```agda
  decodeEncode : ∀ a b p → Path (decode a b (encode a b p)) p
  decodeEncode a _ = 🧊.J (λ b p → Path (decode a b (encode a b p)) p)
    (🧊.cong (decode a a) (encodeRefl a) 🧊.∙ decodeRefl a)
    where open import Cubical.Foundations.Isomorphism

isSetOrd : isSet Ord
isSetOrd a b = isOfHLevelRetract 1 (encode a b) (decode a b)
  (decodeEncode a b) (isPropCover a b) where open OrdSet

isProp≡ : isProp (a ≡ b)
isProp≡ = 🧊.subst isProp PathPathEq (isSetOrd _ _)
```

## 路径集是集合

```agda
module RouteSet where
  open import Cubical.Relation.Nullary
```

```agda
  suc-inv : (p : Route a (suc a)) → Path p suc
  suc-inv {a} p = {! p !}
```

```agda
  discreteRoute : Discrete (Route a b)
  discreteRoute p suc = yes (suc-inv p)
  discreteRoute p (suc₂ q) = {!   !}
  discreteRoute p lim = {!   !}
  discreteRoute p (lim₂ q) = {!   !}
```

## 子树关系

```agda
import Data.Nat.Properties as ℕ
open import Induction.WellFounded
open import Relation.Binary hiding (Rel)
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
```

### 严格序

尊重相等

```agda
<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

传递性

```agda
Rt-trans : Transitive Route
Rt-trans p suc      = suc₂ p
Rt-trans p lim      = lim₂ p
Rt-trans p (suc₂ q) = suc₂ (Rt-trans p q)
Rt-trans p (lim₂ q) = lim₂ (Rt-trans p q)

<-trans : Transitive _<_
<-trans = map2 Rt-trans
```
