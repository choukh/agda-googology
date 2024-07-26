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
  hiding (_≡_; refl; sym; cong; cong₂; subst)
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath; PathPathEq)
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
data Road : Rel
```

**定义** 我们说 $a$ 是 $b$ 的子树, 记作 $a \lt b$, 当且仅当存在一条路径从 $a$ 到 $b$.

```agda
_<_ : Rel; infix 6 _<_
a < b = ∥ Road a b ∥₁
```

**定义** 我们说一个 $f:ℕ→\text{Ord}$ 是严格单调递增序列, 记作 $\text{wf}(f)$, 当且仅当对任意 $n$ 都有 $f(n) < f(n^+)$.

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
data Road where
  zero : Road a (suc a)
  suc  : Road a b → Road a (suc b)
  lim  : ⦃ _ : wf f ⦄ → Road a (f n) → Road a (lim f)
```

### 基本性质

良构条件是命题

```agda
isPropWf : isProp (wf f)
isPropWf = isPropImplicitΠ λ _ → squash₁
```

构造子的单射性

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → Ord.lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

极限的外延性

```agda
limExtPath : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → Path _ (f n) (g n)) → Path Ord (lim f) (lim g)
limExtPath {f} p = 🧊.cong₂ (λ (f : Seq) (wff : wf f) → Ord.lim f ⦃ wff ⦄)
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

## 序数集合

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
  isPropCover zero zero tt tt = 🧊.refl
  isPropCover (suc a) (suc b) = isPropCover a b
  isPropCover (lim f) (lim g) = isPropΠ (λ n → isPropCover (f n) (g n))
```

2. 将 `a b : Ord` 的道路空间 `Path a b` 编码为覆叠空间.

```agda
  encode : ∀ a b → Path _ a b → Cover a b
  encode a b = J (λ b _ → Cover a b) (reflCode a)

  encodeRefl : ∀ a → Path _ (encode a a 🧊.refl) (reflCode a)
  encodeRefl a = JRefl (λ b _ → Cover a b) (reflCode a)
```

3. 将覆叠空间解码为道路空间.

```agda
  decode : ∀ a b → Cover a b → Path _ a b
  decode zero zero _ = 🧊.refl
  decode (suc a) (suc b) p = 🧊.cong suc (decode a b p)
  decode (lim f) (lim g) p = limExtPath λ n → decode (f n) (g n) (p n)

  decodeRefl : ∀ a → Path _ (decode a a (reflCode a)) 🧊.refl
  decodeRefl zero = 🧊.refl
  decodeRefl (suc a) i = 🧊.cong suc (decodeRefl a i)
  decodeRefl (lim f) i = 🧊.cong₂
    (λ (f : Seq) (wff : wf f) → Ord.lim f ⦃ wff ⦄)
    (λ j n → decodeRefl (f n) i j)
    (isSet→SquareP {A = λ i j → wf (λ n → decodeRefl (f n) i j)}
      (λ _ _ → isProp→isSet isPropWf) (toPathP (isPropWf _ _)) 🧊.refl 🧊.refl 🧊.refl i)
```

4. 证明编码与解码互逆, 结合 `Cover a b` 是命题, 说明 `Path a b` 是命题, 也即 `Ord` 是集合.

```agda
  decodeEncode : ∀ a b p → Path _ (decode a b (encode a b p)) p
  decodeEncode a _ = J (λ b p → Path _ (decode a b (encode a b p)) p)
    (🧊.cong (decode a a) (encodeRefl a) ∙ decodeRefl a)
    where open import Cubical.Foundations.Isomorphism

isSetOrd : isSet Ord
isSetOrd a b = isOfHLevelRetract 1 (encode a b) (decode a b)
  (decodeEncode a b) (isPropCover a b) where open OrdSet

isProp≡ : isProp (a ≡ b)
isProp≡ = 🧊.subst isProp PathPathEq (isSetOrd _ _)
```

## 路径与子树关系

```agda
import Data.Nat.Properties as ℕ
open import Induction.WellFounded
open import Relation.Binary hiding (Rel)
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
```

```agda
pattern zero₁  = ∣ zero ∣₁
pattern suc₁ r = ∣ suc r ∣₁
pattern lim₁ r = ∣ lim r ∣₁
```

### 严格序

尊重相等

```agda
Rd-resp-≡ : Road Respects₂ _≡_
Rd-resp-≡ = (λ { refl → id }) , (λ { refl → id })

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

传递性

```agda
Rd-trans : Transitive Road
Rd-trans r zero    = suc r
Rd-trans r (suc s) = suc (Rd-trans r s)
Rd-trans r (lim s) = lim (Rd-trans r s)

<-trans : Transitive _<_
<-trans = map2 Rd-trans
```

良基性

```agda
Rd-acc : Road a b → Acc Road a
Rd-acc zero    = acc λ r → Rd-acc r
Rd-acc (suc r) = acc λ s → Rd-acc (Rd-trans s r)
Rd-acc (lim r) = acc λ s → Rd-acc (Rd-trans s r)

Rd-wellFounded : WellFounded Road
Rd-wellFounded _ = Rd-acc zero
```

```agda
isPropAcc : isProp (Acc _<_ a)
isPropAcc (acc p) (acc q) i = acc (λ x<a → isPropAcc (p x<a) (q x<a) i)

<-acc : a < b → Acc _<_ a
<-acc zero₁    = acc λ r → <-acc r
<-acc (suc₁ r) = acc λ s → <-acc (<-trans s ∣ r ∣₁)
<-acc (lim₁ r) = acc λ s → <-acc (<-trans s ∣ r ∣₁)
<-acc (squash₁ p q i) = isPropAcc (<-acc p) (<-acc q) i

<-wellFounded : WellFounded _<_
<-wellFounded _ = <-acc zero₁
```

良基关系是非对称且反自反的

```agda
Rd-asym : Asymmetric Road
Rd-asym = wf⇒asym Rd-wellFounded

Rd-irrefl : Irreflexive _≡_ Road
Rd-irrefl = wf⇒irrefl Rd-resp-≡ sym Rd-wellFounded
```

```agda
<-asym : Asymmetric _<_
<-asym = wf⇒asym <-wellFounded

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = wf⇒irrefl <-resp-≡ sym <-wellFounded
```

路径关系与子树关系分别构成严格偏序

```agda
Rd-isStrictPartialOrder : ≡.IsStrictPartialOrder Road
Rd-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = Rd-irrefl
  ; trans = Rd-trans
  ; <-resp-≈ = Rd-resp-≡ }

<-isStrictPartialOrder : ≡.IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = <-irrefl
  ; trans = <-trans
  ; <-resp-≈ = <-resp-≡ }
```

### 非严格序

**定义** 非严格序

```agda
open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as NonStrictRoad public using () renaming (_≤_ to infix 6 NSRoad; <⇒≤ to Road→NSRoad)

open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as NonStrictSubTree public using () renaming (_≤_ to infix 6 _≤_; <⇒≤ to <→≤)
```

## 路径集合

```agda
module RoadSet where
  open import Cubical.Data.Nat using (discreteℕ)
  open import Cubical.Relation.Nullary
  open import Cubical.Axiom.UniquenessOfIdentity
```

```agda
  zero-unique : (r : Road a (suc a)) → Path _ r zero
  zero-unique r = aux r 🧊.refl where
    aux : (r : Road a (suc b)) (p : Path _ b a)
      → PathP (λ i → Road a (suc (p i))) r zero
    aux zero = UIP→AxiomK (isSet→UIP isSetOrd) _ _ _ 🧊.refl
    aux (suc r) p = ⊥-elim $ Rd-irrefl (sym $ pathToEq p) r
```

```agda
  Rd-suc-inj : {r s : Road a b} → suc r ≡ suc r → r ≡ s
  Rd-suc-inj p = {! p  !}
```

```agda
  discreteRoad : Discrete (Road a b)
  discreteRoad r zero              = yes (zero-unique r)
  discreteRoad zero (suc r)       = ⊥-elim (Rd-irrefl refl r)
  discreteRoad (suc r) (suc s)  = mapDec (🧊.cong suc) {!   !} (discreteRoad r s)
  discreteRoad (lim {n = n₁} r) (lim {n = n₂} s) with discreteℕ n₁ n₂
  ... | yes p = case pathToEq p of λ { refl →
    mapDec {!   !} {!   !} (discreteRoad r s) }
  ... | no p = no {!   !}
```
