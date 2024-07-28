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
open import Cubical.Foundations.Prelude as 🧊 public
  hiding (_≡_; refl; sym; cong; cong₂; subst)
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
  using (Σ-syntax; ∃-syntax; _×_; fst; snd; _,_; ΣPathP; PathPΣ)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map; map2; rec→Set)
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
open import Bridged.Data.Empty public using (⊥; ⊥-elim; 🧊⊥-elim; isProp⊥)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

## 良构树序数

互归纳定义良构树序数与路径集.

```agda
data Ord : Type
data Road : Ord → Ord → Type
```

**定义** 我们说 $a$ 是 $b$ 的子树, 记作 $a \lt b$, 当且仅当存在一条路径从 $a$ 到 $b$.

```agda
_<_ : Ord → Ord → Type; infix 6 _<_
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
limExtPath p = 🧊.cong₂ (λ f (wff : wf f) → Ord.lim f ⦃ wff ⦄) (funExt p) (toPathP $ isPropWf _ _)

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

## 序数集合

```agda
module OrdSet where
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
    (λ f (wff : wf f) → Ord.lim f ⦃ wff ⦄)
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
open import Relation.Binary
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Cubical.Relation.Nullary
```

```agda
pattern zero₁  = ∣ zero ∣₁
pattern suc₁ r = ∣ suc r ∣₁
pattern lim₁ r = ∣ lim r ∣₁
```

### 严格序

尊重相等

```agda
rd-resp-≡ : Road Respects₂ _≡_
rd-resp-≡ = (λ { refl → id }) , (λ { refl → id })

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

传递性

```agda
rd-trans : Transitive Road
rd-trans r zero    = suc r
rd-trans r (suc s) = suc (rd-trans r s)
rd-trans r (lim s) = lim (rd-trans r s)

<-trans : Transitive _<_
<-trans = map2 rd-trans
```

良基性

```agda
rd-acc : Road a b → Acc Road a
rd-acc zero    = acc λ r → rd-acc r
rd-acc (suc r) = acc λ s → rd-acc (rd-trans s r)
rd-acc (lim r) = acc λ s → rd-acc (rd-trans s r)

rd-wellFounded : WellFounded Road
rd-wellFounded _ = rd-acc zero
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
rd-asym : Asymmetric Road
rd-asym = wf⇒asym rd-wellFounded

rd-irrefl : Irreflexive _≡_ Road
rd-irrefl = wf⇒irrefl rd-resp-≡ sym rd-wellFounded
```

```agda
<-asym : Asymmetric _<_
<-asym = wf⇒asym <-wellFounded

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = wf⇒irrefl <-resp-≡ sym <-wellFounded
```

路径关系与子树关系分别构成严格偏序

```agda
rd-isStrictPartialOrder : ≡.IsStrictPartialOrder Road
rd-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = rd-irrefl
  ; trans = rd-trans
  ; <-resp-≈ = rd-resp-≡ }

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
open import Relation.Binary.Construct.StrictToNonStrict _≡_ Road
  as NonStrictRoad public using () renaming (_≤_ to infix 6 NSRoad; <⇒≤ to rd→ns)

open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as NonStrictSubTree public using () renaming (_≤_ to infix 6 _≤_; <⇒≤ to <→≤)
```

```agda
ns→≤ : NSRoad a b → a ≤ b
ns→≤ (inl r) = inl ∣ r ∣₁
ns→≤ (inr p) = inr p
```

命题性

```agda
isProp≤ : isProp (a ≤ b)
isProp≤ = isProp⊎ squash₁ isProp≡ (flip <-irrefl)
```

严格序与非严格序的相互转化

```agda
rds→ns : Road a (suc b) → NSRoad a b
rds→ns zero    = inr refl
rds→ns (suc p) = inl p

<s→≤ : a < suc b → a ≤ b
<s→≤ = rec isProp≤ (ns→≤ ∘ rds→ns)
```

```agda
ns→rds : NSRoad a b → Road a (suc b)
ns→rds (inl r)    = suc r
ns→rds (inr refl) = zero

≤→<s : a ≤ b → a < suc b
≤→<s (inl r)    = map suc r
≤→<s (inr refl) = zero₁
```

自反性, 反对称性, 传递性

```agda
ns-refl : Reflexive NSRoad
ns-refl = NonStrictRoad.reflexive refl

ns-antisym : Antisymmetric _≡_ NSRoad
ns-antisym = NonStrictRoad.antisym isEquivalence rd-trans rd-irrefl

ns-trans : Transitive NSRoad
ns-trans = NonStrictRoad.trans isEquivalence rd-resp-≡ rd-trans

rd-ns-trans : Trans Road NSRoad Road
rd-ns-trans = NonStrictRoad.<-≤-trans rd-trans (fst rd-resp-≡)

ns-rd-trans : Trans NSRoad Road Road
ns-rd-trans = NonStrictRoad.≤-<-trans sym rd-trans (snd rd-resp-≡)
```

```agda
≤-refl : Reflexive _≤_
≤-refl = NonStrictSubTree.reflexive refl

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = NonStrictSubTree.antisym isEquivalence <-trans <-irrefl

≤-trans : Transitive _≤_
≤-trans = NonStrictSubTree.trans isEquivalence <-resp-≡ <-trans

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans = NonStrictSubTree.<-≤-trans <-trans (fst <-resp-≡)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans = NonStrictSubTree.≤-<-trans sym <-trans (snd <-resp-≡)
```

非严格路径关系与非严格子树关系分别构成非严格偏序

```agda
ns-isPreorder : ≡.IsPreorder NSRoad
ns-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inr
  ; trans = ns-trans
  }

ns-isPartialOrder : ≡.IsPartialOrder NSRoad
ns-isPartialOrder = record { isPreorder = ns-isPreorder ; antisym = ns-antisym }
```

```agda
≤-isPreorder : ≡.IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inr
  ; trans = ≤-trans
  }

≤-isPartialOrder : ≡.IsPartialOrder _≤_
≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }
```

```agda
module RoadReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≡_} {_≤_ = NSRoad} {_<_ = Road}
    ns-isPreorder rd-asym rd-trans rd-resp-≡ rd→ns rd-ns-trans ns-rd-trans
    public

module SubTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
    ≤-isPreorder <-asym <-trans <-resp-≡ <→≤ <-≤-trans ≤-<-trans
    public
```

## 良构序列的性质

```agda
seq-pres< : ⦃ _ : wf f ⦄ → m ℕ.< n → f m < f n
seq-pres< (ℕ.s≤s m≤n) with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inl m<n  = <-trans (seq-pres< m<n) it
... | inr refl = it
```

```agda
seq-pres≤ : ⦃ _ : wf f ⦄ → m ℕ.≤ n → f m ≤ f n
seq-pres≤ m≤n with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inl m<n = inl (seq-pres< m<n)
... | inr refl = inr refl
```

```agda
seq-inj≡ : ∀ f → ⦃ _ : wf f ⦄ → f m ≡ f n → m ≡ n
seq-inj≡ {m} {n} _ eq with ℕ.<-cmp m n
... | tri< m<n _ _  = ⊥-elim $ <-irrefl eq (seq-pres< m<n)
... | tri≈ _ refl _ = refl
... | tri> _ _ n<m  = ⊥-elim $ <-irrefl (sym eq) (seq-pres< n<m)
```

```agda
seq-inj< : ∀ f → ⦃ _ : wf f ⦄ → f m < f n → m ℕ.< n
seq-inj< {m} {n} _ r with ℕ.<-cmp m n
... | tri< m<n _ _  = m<n
... | tri≈ _ refl _ = ⊥-elim $ <-irrefl refl r
... | tri> _ _ n<m  = ⊥-elim $ <-asym r (seq-pres< n<m)
```

```agda
seq-notDense : ∀ f → ⦃ _ : wf f ⦄ → f n < f m → f m < f (suc n) → ⊥
seq-notDense f r s = ℕ.<⇒≱ (seq-inj< f r) (ℕ.m<1+n⇒m≤n (seq-inj< f s))
```

## 子树的三歧性

```agda
isPropConnex : isProp (a < b ⊎ b ≤ a)
isPropConnex = isProp⊎ squash₁ isProp≤ λ r s → <-irrefl refl (<-≤-trans r s)
```

```agda
<-connex-rd : Road a c → Road b c → a < b ⊎ b ≤ a
<-connex-rd zero    zero    = inr $ inr refl
<-connex-rd zero    (suc s) = inr $ inl ∣ s ∣₁
<-connex-rd (suc r) zero    = inl ∣ r ∣₁
<-connex-rd (suc r) (suc s) = <-connex-rd r s
<-connex-rd (lim {n} r) (lim {n = m} s) with ℕ.<-cmp n m
... | tri< n<m _ _  = rec isPropConnex (λ t → <-connex-rd (rd-trans r t) s) (seq-pres< n<m)
... | tri≈ _ refl _ = <-connex-rd r s
... | tri> _ _ m<n  = rec isPropConnex (λ t → <-connex-rd r (rd-trans s t)) (seq-pres< m<n)
```

```agda
<-connex : a < c → b < c → a < b ⊎ b ≤ a
<-connex = rec2 isPropConnex <-connex-rd
```

```agda
<-trich : a < c → b < c → Tri (a < b) (a ≡ b) (b < a)
<-trich r s with <-connex r s
... | inl t       = tri< t (λ p → <-irrefl p t) (<-asym t)
... | inr (inl t) = tri> (<-asym t) (λ p → <-irrefl (sym p) t) t
... | inr (inr p) = tri≈ (λ t → <-irrefl (sym p) t) (sym p) (λ t → <-irrefl p t)
```

## 路径集合

```agda
module RoadSet where
  open import Cubical.Data.Nat using (discreteℕ; isSetℕ)
  open import Cubical.Axiom.UniquenessOfIdentity
```

```agda
  rd-zero-unique : (r : Road a (suc a)) → Path _ r zero
  rd-zero-unique r = aux r 🧊.refl where
    aux : (r : Road a (suc b)) (p : Path _ b a)
      → PathP (λ i → Road a (suc (p i))) r zero
    aux zero = UIP→AxiomK (isSet→UIP isSetOrd) _ _ _ 🧊.refl
    aux (suc r) p = ⊥-elim $ rd-irrefl (sym $ pathToEq p) r
```

```agda
  rd-suc-inj : {r s : Road a b} → suc r ≡ suc s → r ≡ s
  rd-suc-inj refl = refl

  rd-suc-injPath : {r s : Road a b} → Path _ (suc r) (suc s) → Path _ r s
  rd-suc-injPath = eqToPath ∘ rd-suc-inj ∘ pathToEq
```

```agda
  rd-lim-injPath : ⦃ _ : wf f ⦄ {r s : Road a (f n)} → Path (Road a (lim f)) (lim r) (lim s) → Path _ r s
  rd-lim-injPath p = aux (pathToEq p) 🧊.refl where
    aux : ⦃ _ : wf f ⦄ {r : Road a (f n)} {s : Road a (f m)} → Road.lim {f = f} r ≡ lim s
      → (p : Path _ n m) → PathP (λ i → Road a (f (p i))) r s
    aux {f} {a} {r} {s} refl = UIP→AxiomK (isSet→UIP isSetℕ) _ _
      (λ p → PathP (λ i → Road a (f (p i))) r s) 🧊.refl
```

```agda
  discreteRoad : Discrete (Road a b)
  discreteRoad r zero           = yes (rd-zero-unique r)
  discreteRoad zero (suc r)     = ⊥-elim (rd-irrefl refl r)
  discreteRoad (suc r) (suc s)  = mapDec (🧊.cong suc) (λ p q → p (rd-suc-injPath q)) (discreteRoad r s)
  discreteRoad (lim {n = n₁} r) (lim {n = n₂} s) with discreteℕ n₁ n₂
  ... | yes p = case pathToEq p of λ { refl → mapDec (🧊.cong lim) (λ p q → p (rd-lim-injPath q)) (discreteRoad r s) }
  ... | no p = no λ q → case pathToEq q of λ { refl → p 🧊.refl }
```

```agda
isSetRoad : isSet (Road a b)
isSetRoad = Discrete→isSet RoadSet.discreteRoad
```

## 典范路径

```agda
module CanonicalRoad where
  open import Cubical.Foundations.Function using (2-Constant)
```

```agda
  min : (f : Seq) ⦃ wff : wf f ⦄ → a < f n → Σ[ m ∈ ℕ ] a < f m
  min {n = zero} f r = 0 , r
  min {n = suc n} f r with <-connex r it
  ... | inl r = min f r
  ... | inr _ = suc n , r
```

```agda
  min-unique-pre : (f : Seq) ⦃ wff : wf f ⦄ (r : a < f n) (s : a < f (suc m))
    → (f m ≤ a) → Path _ (min f r) (suc m , s)
  min-unique-pre {n = zero}  f r s t = ⊥-elim $ ℕ.n≮0 $ seq-inj< f $ ≤-<-trans t r
  min-unique-pre {n = suc n} f r s t with <-connex r it
  min-unique-pre {n = suc n} f _ s t            | inl r           = min-unique-pre f r s t
  min-unique-pre {n = suc n} f r _ (inr refl)   | inr (inl fn<fm) = ⊥-elim $ seq-notDense f fn<fm r
  min-unique-pre {n = suc n} f _ s (inl fm<fn)  | inr (inr refl)  = ⊥-elim $ seq-notDense f fm<fn s
  min-unique-pre {n = suc n} f r s (inl u)      | inr (inl t)     =
    case n≡m of λ { refl → ΣPathP $ 🧊.refl , squash₁ _ _ } where
    n≡m = ℕ.≤-antisym
      (ℕ.m<1+n⇒m≤n $ seq-inj< f $ <-trans t s)
      (ℕ.m<1+n⇒m≤n $ seq-inj< f $ <-trans u r)
  min-unique-pre {n = suc n} f r s (inr fm≡fn)  | inr (inr refl)  with seq-inj≡ f fm≡fn
  ... | refl = ΣPathP $ 🧊.refl , squash₁ _ _
```

```agda
  min-unique : (f : Seq) ⦃ wff : wf f ⦄ (r : a < f n) (s : a < f m) → Path _ (min f r) (min f s)
  min-unique {n = zero}  {m = zero}  f r s = ΣPathP $ 🧊.refl , squash₁ _ _
  min-unique {n = zero}  {m = suc m} f r s with <-connex s it
  ... | inl s = min-unique f r s
  ... | inr s = ⊥-elim $ ℕ.n≮0 $ seq-inj< f $ ≤-<-trans s r
  min-unique {n = suc n} {m = zero}  f r s with <-connex r it
  ... | inl r = min-unique f r s
  ... | inr r = ⊥-elim $ ℕ.n≮0 $ seq-inj< f $ ≤-<-trans r s
  min-unique {n = suc n} {m = suc m} f r s with <-connex r it | <-connex s it
  ... | inl r           | inl s           = min-unique f r s
  ... | inl r           | inr t           = min-unique-pre f r s t
  ... | inr t           | inl s           = 🧊.sym (min-unique-pre f s r t)
  ... | inr (inl fm<fn) | inr (inr refl)  = ⊥-elim $ seq-notDense f fm<fn r
  ... | inr (inr refl)  | inr (inl fm<fn) = ⊥-elim $ seq-notDense f fm<fn s
  ... | inr (inl t)     | inr (inl u)     =
    case n≡m of λ { refl → ΣPathP $ 🧊.refl , squash₁ _ _ } where
    n≡m = ℕ.≤-antisym
      (ℕ.m<1+n⇒m≤n $ seq-inj< f $ <-trans t s) 
      (ℕ.m<1+n⇒m≤n $ seq-inj< f $ <-trans u r)
  ... | inr (inr refl)  | inr (inr fm≡fn) with seq-inj≡ f fm≡fn
  ... | refl = ΣPathP $ 🧊.refl , squash₁ _ _
```

```agda
  cano : Road a b → Road a b
  <-largeElim : a < b → Road a b

  cano zero = zero
  cano (suc r) = rd-trans (cano r) zero
  cano (lim {f} r) = let (m , s) = min f ∣ r ∣₁ in
    lim {n = m} (cano (<-largeElim s))
```

```agda
  cano-2const : 2-Constant {A = Road a b} cano
  cano-2const zero    r       = case pathToEq (RoadSet.rd-zero-unique r) of λ { refl → 🧊.refl }
  cano-2const (suc r) zero    = ⊥-elim (<-irrefl refl ∣ r ∣₁)
  cano-2const (suc r) (suc s) = 🧊.cong suc (cano-2const r s)
  cano-2const {a} (lim {f} {n} r) (lim {n = m} s) = 🧊.cong₂
    (λ k (t : a < f k) → Road.lim {f = f} {n = k} (cano (<-largeElim t)))
    (🧊.cong fst (min-unique f ∣ r ∣₁ ∣ s ∣₁))
    (🧊.cong snd (min-unique f ∣ r ∣₁ ∣ s ∣₁))
```

```agda
  <-largeElim = rec→Set isSetRoad cano cano-2const
```

```agda
open CanonicalRoad public using (<-largeElim)
```

## 路径的三歧性

一旦建立子树关系到路径关系的消去, 我们可以将子树的三歧性强化为路径的三歧性.

```agda
rd-trich : Road a c → Road b c → Tri (Road a b) (a ≡ b) (Road b a)
rd-trich r s with <-trich ∣ r ∣₁ ∣ s ∣₁
... | tri< t ¬u ¬v = tri< (<-largeElim t) ¬u  (¬v ∘ ∣_∣₁)
... | tri≈ ¬t u ¬v = tri≈ (¬t ∘ ∣_∣₁)     u   (¬v ∘ ∣_∣₁)
... | tri> ¬t ¬u v = tri> (¬t ∘ ∣_∣₁)     ¬u  (<-largeElim v)
```
