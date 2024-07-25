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
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Equality using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
  using (Σ; Σ-syntax; ∃-syntax; _×_; fst; snd; _,_; ΣPathP)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; map)
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

互归纳定义良构树序数与子树关系.

```agda
data Ord : Type
Rel = Ord → Ord → Type
data _<_ : Rel; infix 6 _<_
```

```agda
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

**定义** 子树关系

```agda
data _<_ where
  <suc  : a < suc a
  <suc₂ : a < b → a < suc b
  <lim  : ⦃ _ : wf f ⦄ → f n < lim f
  <lim₂ : ⦃ _ : wf f ⦄ → a < f n → a < lim f
  isProp< : isProp (a < b)
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
isPropWf = isPropImplicitΠ (λ _ → isProp<)
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
isSetOrd a b = isOfHLevelRetract 1 (encode a b) (decode a b) (decodeEncode a b) (isPropCover a b)

isProp≡ : isProp (a ≡ b)
isProp≡ = 🧊.subst isProp PathPathEq (isSetOrd _ _)
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
<-trans : Transitive _<_
<-trans a<b <suc = <suc₂ a<b
<-trans a<f <lim = <lim₂ a<f
<-trans a<b (<suc₂ b<c) = <suc₂ (<-trans a<b b<c)
<-trans a<b (<lim₂ b<f) = <lim₂ (<-trans a<b b<f)
<-trans a<b (isProp< p q i) = isProp< (<-trans a<b p) (<-trans a<b q) i
```

良基性

```agda
isPropAcc : isProp (Acc _<_ a)
isPropAcc (acc p) (acc q) i = acc (λ x<a → isPropAcc (p x<a) (q x<a) i)

<-acc : a < b → Acc _<_ a
<-acc <suc         = acc λ x<a → <-acc x<a
<-acc (<suc₂ a<b)  = acc λ x<a → <-acc (<-trans x<a a<b)
<-acc <lim         = acc λ x<f → <-acc x<f
<-acc (<lim₂ a<f)  = acc λ x<a → <-acc (<-trans x<a a<f)
<-acc (isProp< p q i) = isPropAcc (<-acc p) (<-acc q) i

<-wellFounded : WellFounded _<_
<-wellFounded a = <-acc <suc
```

良基关系是非对称且反自反的

```agda
<-asym : Asymmetric _<_
<-asym = wf⇒asym <-wellFounded

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = wf⇒irrefl <-resp-≡ sym <-wellFounded
```

$\lt$ 构成严格偏序

```agda
<-isStrictPartialOrder : ≡.IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = <-irrefl
  ; trans = <-trans
  ; <-resp-≈ = <-resp-≡ }
```

### 非严格序

命题性

```agda
isProp≤ : isProp (a ≤ b)
isProp≤ = isProp⊎ isProp< isProp≡ (flip <-irrefl)
```

严格序与非严格序的相互转化

```agda
<s→≤ : a < suc b → a ≤ b
<s→≤ <suc = inr refl
<s→≤ (<suc₂ a<b) = inl a<b
<s→≤ (isProp< p q i) = isProp≤ (<s→≤ p) (<s→≤ q) i

≤→<s : a ≤ b → a < suc b
≤→<s (inl p) = <suc₂ p
≤→<s (inr refl) = <suc
```

自反性, 反对称性, 传递性

```agda
≤-refl : Reflexive _≤_
≤-refl = SubTreeLe.reflexive refl

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = SubTreeLe.antisym isEquivalence <-trans <-irrefl

≤-trans : Transitive _≤_
≤-trans = SubTreeLe.trans isEquivalence <-resp-≡ <-trans
```

```agda
<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans = SubTreeLe.<-≤-trans <-trans (fst <-resp-≡)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans = SubTreeLe.≤-<-trans sym <-trans (snd <-resp-≡)
```

$\leq$ 构成非严格偏序

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
module SubTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
    ≤-isPreorder <-asym <-trans <-resp-≡ <→≤ <-≤-trans ≤-<-trans
    public
```

### 不完全的三歧性

```agda
monoseq : ⦃ _ : wf f ⦄ → m ℕ.< n → f m < f n
monoseq (ℕ.s≤s m≤n) with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inl m<n  = <-trans (monoseq m<n) it
... | inr refl = it
```

```agda
injseq : ⦃ _ : wf f ⦄ → f m ≡ f n → m ≡ n
injseq {m} {n} eq with ℕ.<-cmp m n
... | tri< m<n _ _  = ⊥-elim (<-irrefl eq (monoseq m<n))
... | tri≈ _ refl _ = refl
... | tri> _ _ n<m  = ⊥-elim (<-irrefl (sym eq) (monoseq n<m))
```

```agda
<-≥-⊥ : a < b → b ≤ a → ⊥
<-≥-⊥ p q = <-irrefl refl (<-≤-trans p q)
```

```agda
BoundedRel : Rel → Set
BoundedRel _~_ = ∀ {a b c} → a < c → b < c → a ~ b
```

```agda
<-cmp⊎ : BoundedRel λ a b → a < b ⊎ b ≤ a
<-cmp⊎ <suc        <suc         = inr $ inr refl
<-cmp⊎ <suc        (<suc₂ b<a)  = inr $ inl b<a
<-cmp⊎ (<suc₂ a<b) <suc         = inl a<b
<-cmp⊎ (<suc₂ a<c) (<suc₂ b<c)  = <-cmp⊎ a<c b<c
<-cmp⊎ (<lim {n = m}) (<lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inl $ monoseq m<n
... | tri≈ _ refl _ = inr $ inr refl
... | tri> _ _ n<m  = inr $ inl $ monoseq n<m
<-cmp⊎ (<lim {n = m}) (<lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (monoseq m<n) b<f
... | tri≈ _ refl _ = inr $ inl b<f
... | tri> _ _ n<m  = inr $ inl $ <-trans b<f $ monoseq n<m
<-cmp⊎ (<lim₂ {n = m} a<f) (<lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inl $ <-trans a<f $ monoseq m<n
... | tri≈ _ refl _ = inl a<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (monoseq n<m)
<-cmp⊎ (<lim₂ {n = m} a<f) (<lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (<-trans a<f (monoseq m<n)) b<f
... | tri≈ _ refl _ = <-cmp⊎ a<f b<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (<-trans b<f (monoseq n<m))
<-cmp⊎ (isProp< p q i) r = isProp⊎ isProp< isProp≤ <-≥-⊥ (<-cmp⊎ p r) (<-cmp⊎ q r) i
<-cmp⊎ r (isProp< p q i) = isProp⊎ isProp< isProp≤ <-≥-⊥ (<-cmp⊎ r p) (<-cmp⊎ r q) i
```

```agda
<-cmp : BoundedRel λ a b → Tri (a < b) (a ≡ b) (b < a)
<-cmp p q with <-cmp⊎ p q
... | inl a<b = tri< a<b (λ { refl → <-irrefl refl a<b }) (<-asym a<b)
... | inr (inl b<a) = tri> (<-asym b<a) (λ { refl → <-irrefl refl b<a }) b<a
... | inr (inr refl) = tri≈ (<-irrefl refl) refl (<-irrefl refl)
```

**定义** 给定 $a$ 和 $b$, 同时满足 $a \lt c$ 和 $b \lt c$ 的 $c$ 称为 $a$ 和 $b$ 的同株集. 如果它非空, 则称 $a$ 和 $b$ 同株.

```agda
Homo : Rel
Homo a b = Σ[ c ∈ Ord ] (a ≤ c × b ≤ c)
```

```agda
homo-refl : Homo a a
homo-refl = _ , ≤-refl , ≤-refl

homo-sym : Homo a b → Homo b a
homo-sym (c , a≤c , b≤c) = c , b≤c , a≤c
```

注意同株不是传递关系.

```agda
homo-weaken : {A : Set} → (∀ {x} → a < x → b < x → A) → (Homo a b → A)
homo-weaken H (c , inl p     , inl q)     = H {c} p q
homo-weaken H (c , inl p     , inr refl)  = H {suc c} (<-trans p <suc) <suc
homo-weaken H (c , inr refl  , inl q)     = H {suc c} <suc (<-trans q <suc)
homo-weaken H (c , inr refl  , inr refl)  = H {suc c} <suc <suc
```

```agda
<-trich : Homo a b → Tri (a < b) (a ≡ b) (b < a)
<-trich = homo-weaken <-cmp

≤-total : Homo a b → a ≤ b ⊎ b ≤ a
≤-total p with <-trich p
... | tri< p _ _ = inl (inl p)
... | tri≈ _ p _ = inl (inr p)
... | tri> _ _ p = inr (inl p)
```

## 序数函数

```agda
Func : Set
Func = Ord → Ord
variable F : Func
```

```agda
_inflates_ : Func → Rel → Set
F inflates _~_ = ∀ {x} → x ~ F x

infl<→infl≤ : F inflates _<_ → F inflates _≤_
infl<→infl≤ p = <→≤ p
```

```agda
_preserves_ : Func → Rel → Set
F preserves _~_ = ∀ {x y} → x ~ y → F x ~ F y
```

```agda
pres<→pres≤ : F preserves _<_ → F preserves _≤_
pres<→pres≤ pres (inl p)    = <→≤ (pres p)
pres<→pres≤ pres (inr refl) = inr refl
```

```agda
_injects_ : Func → Rel → Set
F injects _~_ = ∀ {x y} → F x ~ F y → x ~ y
```

```agda
inj<→inj≤ : F injects _≡_ → F injects _<_ → F injects _≤_
inj<→inj≤ inj inj< (inl p) = inl (inj< p)
inj<→inj≤ inj inj< (inr p) = inr (inj p)
```

```agda
continuous : F preserves _<_ → Set
continuous {F} pres = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘ f) ⦃ pres it ⦄
```

### 后继运算的性质

```agda
s<s : suc preserves _<_
<→s≤ : a < b → suc a ≤ b

s<s <suc            = <suc
s<s (<suc₂ x<y)     = <suc₂ (s<s x<y)
s<s (<lim {f} {n})  = <suc₂ $ begin-strict
  suc (f n)         <⟨ s<s it ⟩
  suc (f (suc n))   ≤⟨ <→s≤ <lim ⟩
  lim f             ∎ where open SubTreeReasoning
s<s {x} (<lim₂ {f} {n} x<f) = <suc₂ $ begin-strict
  suc x             <⟨ s<s x<f ⟩
  suc (f n)         ≤⟨ <→s≤ <lim ⟩
  lim f             ∎ where open SubTreeReasoning
s<s (isProp< p q i) = isProp< (s<s p) (s<s q) i

<→s≤ <suc = inr refl
<→s≤ (<suc₂ p) = inl (s<s p)
<→s≤ (<lim {f} {n}) = inl $ <lim₂ $ begin-strict
  suc (f n)         <⟨ s<s it ⟩
  suc (f (suc n))   ≤⟨ <→s≤ it ⟩
  f (2+ n)          ∎ where open SubTreeReasoning
<→s≤ {a} (<lim₂ {f} {n} a<f) = inl $ <lim₂ $ begin-strict
  suc a             <⟨ s<s a<f ⟩
  suc (f n)         ≤⟨ <→s≤ it ⟩
  f (suc n)         ∎ where open SubTreeReasoning
<→s≤ (isProp< p q i) = isProp≤ (<→s≤ p) (<→s≤ q) i
```

```agda
s<s-inj : suc injects _<_
s<s-inj <suc        = <suc
s<s-inj (<suc₂ s<b) = <-trans <suc s<b
s<s-inj (isProp< p q i) = isProp< (s<s-inj p) (s<s-inj q) i
```

```agda
≮z : a < 0 → ⊥
≮z (isProp< p q i) = isProp⊥ (≮z p) (≮z q) i
```

```agda
s≤→< : suc a ≤ b → a < b
s≤→< {b = zero}  (inl p) = ⊥-elim (≮z p)
s≤→< {b = suc _} (inl p) = <suc₂ (s<s-inj p)
s≤→< {b = lim _} (inl p) = <-trans <suc p
s≤→< (inr refl) = <suc
```

推论

```agda
s≤s : suc preserves _≤_
s≤s = pres<→pres≤ s<s

s≤s-inj : suc injects _≤_
s≤s-inj = inj<→inj≤ suc-inj s<s-inj
```

```agda
s<l : ⦃ _ : wf f ⦄ → a < lim f → suc a < lim f
s<l {f} (<lim {n}) = begin-strict
  suc (f n) ≤⟨ <→s≤ it ⟩
  f (suc n) <⟨ <lim ⟩
  lim f     ∎ where open SubTreeReasoning
s<l {f} {a} (<lim₂ {n} p) = begin-strict
  suc a     <⟨ s<s p ⟩
  suc (f n) ≤⟨ <→s≤ <lim ⟩
  lim f     ∎ where open SubTreeReasoning
s<l (isProp< p q i) = isProp< (s<l p) (s<l q) i
```

```agda
l≤p : ⦃ _ : wf f ⦄ → lim f ≤ suc a → lim f ≤ a
l≤p (inl <suc) = inr refl
l≤p (inl (<suc₂ p)) = inl p
l≤p (inl (isProp< p q i)) = isProp≤ (l≤p (inl p)) (l≤p (inl q)) i
```

## 最小的极限序数

引理

```agda
z<s : 0 < suc a
z<b : a < b → 0 < b

z<s {(zero)} = <suc
z<s {suc _} = <suc₂ z<s
z<s {lim _} = <suc₂ (<lim₂ {n = 1} (z<b it))

z<b <suc = z<s
z<b (<suc₂ _)  = z<s
z<b (<lim {n}) = <lim₂ {n = suc n} (z<b it)
z<b (<lim₂ _)  = <lim₂ {n = 1} (z<b it)
z<b (isProp< p q i) = isProp< (z<b p) (z<b q) i
```

```agda
z<l : ⦃ _ : wf f ⦄ → 0 < lim f
z<l = <lim₂ {n = 1} (z<b it)
```

```agda
z≤ : 0 ≤ a
z≤ {(zero)} = inr refl
z≤ {suc _}  = inl z<s
z≤ {lim _}  = inl z<l
```

```agda
private instance
  wf-fin : wf fin
  wf-fin = <suc
```

```agda
ω : Ord
ω = lim fin
```

```agda
n<ω : fin n < ω
n<ω {n = zero}  = z<l
n<ω {n = suc n} = s<l n<ω
```

```agda
n≤fn : ∀ f → ⦃ _ : wf f ⦄ → fin n ≤ f n
n≤fn {n = zero} f   = z≤
n≤fn {n = suc n} f  = begin
  fin (suc n)       ≤⟨ s≤s (n≤fn f) ⟩
  suc (f n)         ≤⟨ <→s≤ it ⟩
  f (suc n)         ∎ where open SubTreeReasoning
```

```agda
lim-inv : ⦃ _ : wf f ⦄ → a < lim f → ∃[ n ∈ ℕ ] a < f n
lim-inv <lim      = ∣ _ , it ∣₁
lim-inv (<lim₂ p) = ∣ _ , p ∣₁
lim-inv (isProp< p q i) = squash₁ (lim-inv p) (lim-inv q) i
```

```agda
ω≤l : ⦃ _ : wf f ⦄ → Homo ω (lim f) → ω ≤ lim f
ω≤l {f} homo with <-trich homo
... | tri< < _ _ = inl <
... | tri≈ _ ≡ _ = inr ≡
... | tri> _ _ > = rec isProp≤ aux (lim-inv >) where
  aux : Σ[ n ∈ ℕ ] lim f < fin n → ω ≤ lim f
  aux (n , p) = ⊥-elim $ <-irrefl refl $ begin-strict
    fin n     ≤⟨ n≤fn f ⟩
    f n       <⟨ <lim ⟩
    lim f     <⟨ p ⟩
    fin n     ∎ where open SubTreeReasoning
```

```agda
fin-inj : fin m ≡ fin n → m ≡ n
fin-inj {(zero)} {(zero)} eq = refl
fin-inj {suc m}  {suc n}  eq = cong suc $ fin-inj $ suc-inj eq
```

```agda
fin-suj : a < ω → Σ[ n ∈ ℕ ] fin n ≡ a
fin-suj {(zero)} _  = 0 , refl
fin-suj {suc a} s<ω with fin-suj (<-trans <suc s<ω)
... | (n , refl)    = suc n , refl
fin-suj {lim f} l<ω = ⊥-elim $ <-irrefl refl $ begin-strict
  ω                 ≤⟨ ω≤l $ ω , inr refl , inl l<ω ⟩
  lim f             <⟨ l<ω ⟩
  ω                 ∎ where open SubTreeReasoning
```

```agda
ℕ≡ω : ℕ ≡ Σ Ord (_< ω)
ℕ≡ω = pathToEq $ isoToPath $ iso
  (λ n → fin n , n<ω) (λ (a , a<ω) → fst (fin-suj a<ω))
  (λ a → ΣPathP $ eqToPath (snd $ fin-suj _) , toPathP (isProp< _ _))
  (λ n → eqToPath $ fin-inj $ snd $ fin-suj _)
```

## 可迭代函数
