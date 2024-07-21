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
{-# OPTIONS --safe --lossy-unification #-}
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
open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded using (Acc; acc; WellFounded)
```

## 良构树序数

互归纳定义良构树序数与子树关系.

```agda
data Ord : Set
Rel = Ord → Ord → Set
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

**定义** 严格单调递增序列

```agda
Seq : Set
Seq = ℕ → Ord

wf : Seq → Set
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

z<s {(zero)} = <suc
z<s {suc _} = <suc₂ z<s
z<s {lim _} = <suc₂ (<lim₂ {n = 1} (z<b it))

z<b <suc = z<s
z<b (<suc₂ _)  = z<s
z<b (<lim {n}) = <lim₂ {n = suc n} (z<b it)
z<b (<lim₂ _)  = <lim₂ {n = 1} (z<b it)
```

```agda
z<l : ⦃ _ : wf f ⦄ → 0 < lim f
z<l = <lim₂ {n = 1} (z<b it)
```

```agda
z≤ : 0 ≤ a
z≤ {(zero)} = inj₂ refl
z≤ {suc _}  = inj₁ z<s
z≤ {lim _}  = inj₁ z<l
```

```agda
fs-nz : ∀ f → ⦃ _ : wf f ⦄ → NonZero (f (suc n))
fs-nz _ = nz-intro (z<b it)
```

```agda
nz-elim : ⦃ NonZero a ⦄ → 0 < a
nz-elim {suc a} = z<s
nz-elim {lim f} = z<l
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
infl<→infl≤ p = <⇒≤ p
```

```agda
_preserves_ : Func → Rel → Set
F preserves _~_ = ∀ {x y} → x ~ y → F x ~ F y
```

```agda
pres<→pres≤ : F preserves _<_ → F preserves _≤_
pres<→pres≤ pres (inj₁ p)    = <⇒≤ (pres p)
pres<→pres≤ pres (inj₂ refl) = inj₂ refl
```

```agda
_injects_ : Func → Rel → Set
F injects _~_ = ∀ {x y} → F x ~ F y → x ~ y
```

```agda
inj<→inj≤ : F injects _≡_ → F injects _<_ → F injects _≤_
inj<→inj≤ inj inj< (inj₁ p) = inj₁ (inj< p)
inj<→inj≤ inj inj< (inj₂ p) = inj₂ (inj p)
```

```agda
continuous : F preserves _<_ → Set
continuous {F} pres = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘ f) ⦃ pres it ⦄
```

## 子树关系

```agda
open import Relation.Binary.Structures {A = Ord} _≡_ as ≡
```

### 严格偏序

```agda
<-trans : Transitive _<_
<-trans a<b <suc = <suc₂ a<b
<-trans a<f <lim = <lim₂ a<f
<-trans a<b (<suc₂ b<c) = <suc₂ (<-trans a<b b<c)
<-trans a<b (<lim₂ b<f) = <lim₂ (<-trans a<b b<f)
```

```agda
suc-inv : a < suc b → a ≤ b
suc-inv <suc = inj₂ refl
suc-inv (<suc₂ a<b) = inj₁ a<b
```

```agda
lim-inv : ⦃ _ : wf f ⦄ → a < lim f → ∃[ n ] a < f n
lim-inv <lim   = _ , it
lim-inv (<lim₂ a<f) = _ , a<f
```

```agda
<-irrefl : Irreflexive _≡_ _<_
<-irrefl {suc a} refl s<s with suc-inv s<s
... | inj₁ s<a = <-irrefl refl (<-trans <suc s<a)
<-irrefl {lim _} refl l<l with lim-inv l<l
... | n , l<f = <-irrefl refl (<-trans <lim l<f)
```

```agda
<-asym : Asymmetric _<_
<-asym = trans∧irr⇒asym {_≈_ = _≡_} refl <-trans <-irrefl
```

```agda
<-notDense : a < b → b ≮ suc a
<-notDense p <suc = <-irrefl refl p
<-notDense p (<suc₂ q) = <-asym p q
```

```agda
<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

```agda
<-isStrictPartialOrder : ≡.IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = <-irrefl
  ; trans = <-trans
  ; <-resp-≈ = <-resp-≡ }
```

```
monoseq : ⦃ _ : wf f ⦄ → m ℕ.< n → f m < f n
monoseq (ℕ.s≤s m≤n) with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n  = <-trans (monoseq m<n) it
... | inj₂ refl = it
```

```agda
injseq : ⦃ _ : wf f ⦄ → f m ≡ f n → m ≡ n
injseq {m} {n} eq with ℕ.<-cmp m n
... | tri< m<n _ _  = ⊥-elim (<-irrefl eq (monoseq m<n))
... | tri≈ _ refl _ = refl
... | tri> _ _ n<m  = ⊥-elim (<-irrefl (sym eq) (monoseq n<m))
```

### 非严格偏序

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
<-≤-trans = SubTreeLe.<-≤-trans <-trans (proj₁ <-resp-≡)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans = SubTreeLe.≤-<-trans sym <-trans (proj₂ <-resp-≡)
```

```agda
≤-isPreorder : ≡.IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inj₂
  ; trans = ≤-trans
  }

≤-isPartialOrder : ≡.IsPartialOrder _≤_
≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }
```

```agda
module SubTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<_}
    ≤-isPreorder <-asym <-trans <-resp-≡ <⇒≤ <-≤-trans ≤-<-trans
    public
```

### 不完全的三歧性

```agda
BoundedRel : Rel → Set
BoundedRel _~_ = ∀ {a b c} → a < c → b < c → a ~ b
```

```agda
<-cmp⊎ : BoundedRel λ a b → a < b ⊎ a ≡ b ⊎ b < a
<-cmp⊎ <suc        <suc         = inj₂ $ inj₁ refl
<-cmp⊎ <suc        (<suc₂ b<a)  = inj₂ $ inj₂ b<a
<-cmp⊎ (<suc₂ a<b) <suc         = inj₁ a<b
<-cmp⊎ (<suc₂ a<c) (<suc₂ b<c)  = <-cmp⊎ a<c b<c
<-cmp⊎ (<lim {n = m}) (<lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inj₁ $ monoseq m<n
... | tri≈ _ refl _ = inj₂ $ inj₁ refl
... | tri> _ _ n<m  = inj₂ $ inj₂ $ monoseq n<m
<-cmp⊎ (<lim {n = m}) (<lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (monoseq m<n) b<f
... | tri≈ _ refl _ = inj₂ $ inj₂ b<f
... | tri> _ _ n<m  = inj₂ $ inj₂ $ <-trans b<f $ monoseq n<m
<-cmp⊎ (<lim₂ {n = m} a<f) (<lim {n}) with ℕ.<-cmp m n
... | tri< m<n _ _  = inj₁ $ <-trans a<f $ monoseq m<n
... | tri≈ _ refl _ = inj₁ a<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (monoseq n<m)
<-cmp⊎ (<lim₂ {n = m} a<f) (<lim₂ {n} b<f) with ℕ.<-cmp m n
... | tri< m<n _ _  = <-cmp⊎ (<-trans a<f (monoseq m<n)) b<f
... | tri≈ _ refl _ = <-cmp⊎ a<f b<f
... | tri> _ _ n<m  = <-cmp⊎ a<f (<-trans b<f (monoseq n<m))
```

```agda
<-cmp : BoundedRel λ a b → Tri (a < b) (a ≡ b) (b < a)
<-cmp p q with <-cmp⊎ p q
... | inj₁ a<b = tri< a<b (λ { refl → <-irrefl refl a<b }) (<-asym a<b)
... | inj₂ (inj₁ refl) = tri≈ (<-irrefl refl) refl (<-irrefl refl)
... | inj₂ (inj₂ b<a) = tri> (<-asym b<a) (λ { refl → <-irrefl refl b<a }) b<a
```

**定义** 同株

```agda
_≘_ : Rel
a ≘ b = ∃[ c ] a ≤ c × b ≤ c
```

```agda
≘-refl : a ≘ a
≘-refl = _ , ≤-refl , ≤-refl

≘-sym : a ≘ b → b ≘ a
≘-sym (c , a≤c , b≤c) = c , b≤c , a≤c
```

注意同株不是传递关系.

```agda
≘-weaken : {A : Set} → (∀ {x} → a < x → b < x → A) → (a ≘ b → A)
≘-weaken H (c , inj₁ p     , inj₁ q)     = H {c} p q
≘-weaken H (c , inj₁ p     , inj₂ refl)  = H {suc c} (<-trans p <suc) <suc
≘-weaken H (c , inj₂ refl  , inj₁ q)     = H {suc c} <suc (<-trans q <suc)
≘-weaken H (c , inj₂ refl  , inj₂ refl)  = H {suc c} <suc <suc
```

```agda
<-trich : a ≘ b → Tri (a < b) (a ≡ b) (b < a)
<-trich = ≘-weaken <-cmp

≤-total : a ≘ b → a ≤ b ⊎ b ≤ a
≤-total p with <-trich p
... | tri< p _ _ = inj₁ (inj₁ p)
... | tri≈ _ p _ = inj₁ (inj₂ p)
... | tri> _ _ p = inj₂ (inj₁ p)
```

### 良基性

```agda
<-acc : a < b → Acc _<_ a
<-acc <suc         = acc λ x<a → <-acc x<a
<-acc (<suc₂ a<b)  = acc λ x<a → <-acc (<-trans x<a a<b)
<-acc <lim         = acc λ x<f → <-acc x<f
<-acc (<lim₂ a<f)  = acc λ x<a → <-acc (<-trans x<a a<f)
```

```agda
<-wellFounded : WellFounded _<_
<-wellFounded a = <-acc <suc
```

### 更多性质

后继运算的保序性

```agda
s<s : suc preserves _<_
<→s≤ : a < b → suc a ≤ b

s<s <suc           = <suc
s<s (<suc₂ x<y)    = <suc₂ (s<s x<y)
s<s (<lim {f} {n}) = <suc₂ $ begin-strict
  suc (f n)       <⟨ s<s it ⟩
  suc (f (suc n)) ≤⟨ <→s≤ <lim ⟩
  lim f           ∎ where open SubTreeReasoning
s<s {x} (<lim₂ {f} {n} x<f) = <suc₂ $ begin-strict
  suc x           <⟨ s<s x<f ⟩
  suc (f n)       ≤⟨ <→s≤ <lim ⟩
  lim f           ∎ where open SubTreeReasoning

<→s≤ <suc = inj₂ refl
<→s≤ (<suc₂ p) = inj₁ (s<s p)
<→s≤ (<lim {f} {n}) = inj₁ $ <lim₂ $ begin-strict
  suc (f n)       <⟨ s<s it ⟩
  suc (f (suc n)) ≤⟨ <→s≤ it ⟩
  f (2+ n)        ∎ where open SubTreeReasoning
<→s≤ {a} (<lim₂ {f} {n} a<f) = inj₁ $ <lim₂ $ begin-strict
  suc a           <⟨ s<s a<f ⟩
  suc (f n)       ≤⟨ <→s≤ it ⟩
  f (suc n)       ∎ where open SubTreeReasoning
```

```agda
s<s-inj : suc injects _<_
s<s-inj <suc        = <suc
s<s-inj (<suc₂ s<b) = <-trans <suc s<b
```

```agda
s≤→< : suc a ≤ b → a < b
s≤→< {b = suc _} (inj₁ p) = <suc₂ (s<s-inj p)
s≤→< {b = lim _} (inj₁ p) with lim-inv p
... | _ , p = <lim₂ (<-trans <suc p)
s≤→< (inj₂ refl) = <suc
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
```

```agda
l≤p : ⦃ _ : wf f ⦄ → lim f ≤ suc a → lim f ≤ a
l≤p (inj₁ <suc) = inj₂ refl
l≤p (inj₁ (<suc₂ p)) = inj₁ p
```

## 最小的极限序数

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
n<fs : ∀ f n → ⦃ _ : wf f ⦄ → fin n < f (suc n)
n<fs f _ = ≤-<-trans (n≤fn f) it
```

```agda
ω≤l : ⦃ _ : wf f ⦄ → ω ≘ lim f → ω ≤ lim f
ω≤l {f} homo with <-trich homo
... | tri< < _ _ = inj₁ <
... | tri≈ _ ≡ _ = inj₂ ≡
... | tri> _ _ > with lim-inv >
... | n , l<n = ⊥-elim $ <-irrefl refl $ begin-strict
  fin n ≤⟨ n≤fn f ⟩
  f n   <⟨ <lim ⟩
  lim f <⟨ l<n ⟩
  fin n ∎ where open SubTreeReasoning
```

```agda
fin-inj : fin m ≡ fin n → m ≡ n
fin-inj {(zero)} {(zero)} eq = refl
fin-inj {suc m}  {suc n}  eq = cong suc $ fin-inj $ suc-inj eq
```

```agda
fin-suj : a < ω → ∃[ n ] fin n ≡ a
fin-suj {(zero)} _ = 0 , refl
fin-suj {suc a} s<ω with fin-suj (<-trans <suc s<ω)
... | n , refl = suc n , refl
fin-suj {lim f} l<ω = ⊥-elim $ <-irrefl refl $ begin-strict
  ω     ≤⟨ ω≤l (ω , inj₂ refl , inj₁ l<ω) ⟩
  lim f <⟨ l<ω ⟩
  ω     ∎ where open SubTreeReasoning
```

```agda
ℕ↪ω : ℕ ↪ Σ _ (_< ω)
ℕ↪ω = record
  { to        = λ n → fin n , n<ω
  ; from      = λ (a , a<ω) → proj₁ (fin-suj a<ω)
  ; to-cong   = λ { refl → refl }
  ; from-cong = λ { refl → refl }
  ; inverseʳ  = λ { refl → fin-inj $ proj₂ $ fin-suj n<ω }
  }
```

## 跨树关系

```agda
infix 4 _≼_ _⋠_ _≺_ _≃_
data _≼_ : Rel
_⋠_ _≺_ _≃_ : Rel
a ⋠ b = ¬ a ≼ b
a ≺ b = suc a ≼ b
a ≃ b = a ≼ b × b ≼ a
```

### 前驱

**定义** 前驱深度

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc a) = ⊤ ⊎ Depth a
Depth (lim f) = Σ ℕ λ n → Depth (f n)

private variable δ : Depth a
```

**定义** 前驱运算

```agda
_∸_ : ∀ a → Depth a → Ord; infixl 6 _∸_
suc a ∸ inj₁ tt = a
suc a ∸ inj₂ δ  = a ∸ δ
lim f ∸ (n , δ) = f n ∸ δ
```

### 非严格偏序

```agda
data _≼_ where
  z≼ : zero ≼ b
  s≼ : a ≼ b ∸ δ → a ≺ b
  l≼ : ⦃ _ : wf f ⦄ → (∀ {n} → f n ≼ b) → lim f ≼ b
```

```agda
≺⇒≼ : _≺_ ⇒ _≼_
≺⇒≼ (s≼ z≼) = z≼
≺⇒≼ (s≼ (s≼ p)) = s≼ (≺⇒≼ (s≼ p))
≺⇒≼ (s≼ (l≼ p)) = l≼ (≺⇒≼ (s≼ p))
```

```agda
s≼s : a ≼ b → suc a ≼ suc b
s≼s = s≼ {δ = inj₁ tt}
```

```agda
s≼s-inj : suc a ≼ suc b → a ≼ b
s≼s-inj (s≼ {δ = inj₁ tt} p) = p
s≼s-inj (s≼ {δ = inj₂ δ } p) = ≺⇒≼ (s≼ {δ = δ} p)
```

```agda
≼l : ⦃ _ : wf f ⦄ → a ≼ f n → a ≼ lim f
≼l z≼ = z≼
≼l {n} (s≼ {δ} p) = s≼ {δ = n , δ} p
≼l (l≼ p) = l≼ (≼l p)
```

```agda
l≼l : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ {n} → f n ≼ g n) → lim f ≼ lim g
l≼l f≼g = l≼ (≼l f≼g)
```

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc _}  = s≼s ≼-refl
≼-refl {lim _}  = l≼l ≼-refl
```

```agda
≼-trans : Transitive _≼_
≼-trans z≼ _ = z≼
≼-trans p@(s≼ _) (s≼ q) = s≼ (≼-trans (s≼s-inj p) q)
≼-trans (s≼ {δ = n , δ} p) (l≼ q) = ≼-trans (s≼ {δ = δ} p) q
≼-trans (l≼ p) q = l≼ (≼-trans p q)
```

```agda
≼-antisym : Antisymmetric _≃_ _≼_
≼-antisym = _,_
```

### 外延相等

```agda
≃-refl : Reflexive _≃_
≃-refl = ≼-refl , ≼-refl

≃-sym : Symmetric _≃_
≃-sym (p , q) = q , p

≃-trans : Transitive _≃_
≃-trans (p , q) (u , v) = ≼-trans p u , ≼-trans v q
```

```agda
s≃s : a ≃ b → suc a ≃ suc b
s≃s (p , q) = s≼s p , s≼s q

s≃s-inj : suc a ≃ suc b → a ≃ b
s≃s-inj (p , q) = s≼s-inj p , s≼s-inj q
```

```agda
l≃l : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ {n} → f n ≃ g n) → lim f ≃ lim g
l≃l f≃g = (l≼l (proj₁ f≃g)) , (l≼l (proj₂ f≃g))
```

### 严格偏序

```agda
s⋠z : suc a ⋠ 0
s⋠z (s≼ {δ = ⊥} ≼) = ⊥

s⋠ : suc a ⋠ a
s⋠ {(zero)} = s⋠z
s⋠ {suc _} p = s⋠ (s≼s-inj p)
s⋠ {lim _} (s≼ {δ = n , δ} (l≼ p)) = s⋠ (s≼ {δ = δ} p)
```

```agda
≺-irrefl : Irreflexive _≃_ _≺_
≺-irrefl (p , q) r = s⋠ (≼-trans r q)

≺-trans : Transitive _≺_
≺-trans p q = ≼-trans p (≺⇒≼ q)

≺-asym : Asymmetric _≺_
≺-asym p q = ≺-irrefl ≃-refl (≺-trans p q)
```

```agda
≺-≼-trans : Trans _≺_ _≼_ _≺_
≺-≼-trans p q = ≼-trans p q

≼-≺-trans : Trans _≼_ _≺_ _≺_
≼-≺-trans p q = ≼-trans (s≼s p) q
```

```agda
≺-resp-≃ : _≺_ Respects₂ _≃_
≺-resp-≃ = (λ (p , _) q → ≺-≼-trans q p) , (λ (_ , p) q → ≼-≺-trans p q)
```

```agda
open import Relation.Binary.Structures _≃_ as ≃

≃-isEquivalence : ≃.IsEquivalence
≃-isEquivalence = record
  { refl  = ≃-refl
  ; sym   = ≃-sym
  ; trans = ≃-trans
  }

≼-isPreorder : ≃.IsPreorder _≼_
≼-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive = proj₁
  ; trans = ≼-trans
  }

≼-isPartialOrder : ≃.IsPartialOrder _≼_
≼-isPartialOrder = record
  { isPreorder = ≼-isPreorder
  ; antisym = ≼-antisym
  }

≺-isStrictPartialOrder : ≃.IsStrictPartialOrder _≺_
≺-isStrictPartialOrder = record
  { isEquivalence = ≃-isEquivalence
  ; irrefl = ≺-irrefl
  ; trans = ≺-trans
  ; <-resp-≈ = ≺-resp-≃
  }
```

```agda
module CrossTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≃_} {_≤_ = _≼_} {_<_ = _≺_}
    ≼-isPreorder ≺-asym ≺-trans ≺-resp-≃ ≺⇒≼ ≺-≼-trans ≼-≺-trans
    public
```

### 诉诸子树

```agda
≺s : a ≺ suc a
≺s = s≼s ≼-refl

≼s : a ≼ suc a
≼s = ≺⇒≼ ≺s
```

```agda
f≼l : ⦃ _ : wf f ⦄ → f n ≼ lim f
f≼l = ≼l ≼-refl

≺l : ⦃ _ : wf f ⦄ → a ≺ f n → a ≺ lim f
≺l = ≼l
```

```agda
<⇒≺ : _<_ ⇒ _≺_
f≺l : ⦃ _ : wf f ⦄ → f n ≺ lim f
f≺l = ≺-≼-trans (<⇒≺ it) f≼l

<⇒≺ <suc = ≺s
<⇒≺ (<suc₂ p) = ≺-trans (<⇒≺ p) ≺s
<⇒≺ <lim = f≺l
<⇒≺ (<lim₂ p) = ≺l (<⇒≺ p)

≤⇒≼ : _≤_ ⇒ _≼_
≤⇒≼ (inj₁ <suc) = ≼s
≤⇒≼ (inj₁ (<suc₂ p)) = ≼-trans (≺⇒≼ (<⇒≺ p)) ≼s
≤⇒≼ (inj₁ <lim) = f≼l
≤⇒≼ (inj₁ (<lim₂ p)) = ≼l (≺⇒≼ (<⇒≺ p))
≤⇒≼ (inj₂ refl) = ≼-refl
```

```agda
≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = ≃-refl
```

```agda
l≼l-suc : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ {n} → f (suc n) ≼ g (suc n)) → lim f ≼ lim g
l≼l-suc {f} {g} f≼g = l≼ $ λ {n} → ≼l $ begin
  f n                                   ≤⟨ ≤⇒≼ $ <⇒≤ it ⟩
  f (suc n)                             ≤⟨ f≼g ⟩
  g (suc n)                             ∎ where open CrossTreeReasoning

l≃l-suc : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ {n} → f (suc n) ≃ g (suc n)) → lim f ≃ lim g
l≃l-suc f≃g = (l≼l-suc (proj₁ f≃g)) , (l≼l-suc (proj₂ f≃g))
```

外延相等的实例

```agda
ω′ : Ord
ω′ = lim (fin ∘ suc)
```

```agda
_ : ω ≃ ω′
_ = (l≼ $ ≼l $ ≤⇒≼ $ inj₁ it)
  , (l≼ $ ≼l $ ≤⇒≼ $ inj₁ it)
```

## 可迭代函数

```agda
record Normal : Set where
  constructor normal
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<

  private G = _[_]
  nml→infl≼ : G inflates _≼_
  nml→infl≼ {(zero)} = z≼
  nml→infl≼ {suc a} =         begin
    suc a                     ≤⟨ s≼s nml→infl≼ ⟩
    suc (G a)                 ≤⟨ <⇒≺ (pres< <suc) ⟩
    G (suc a)                 ∎ where open CrossTreeReasoning
  nml→infl≼ {lim f} =         l≼ $ begin
    f _                       ≤⟨ ≼l ⦃ pres< it ⦄ nml→infl≼ ⟩
    lim (G ∘ f) ⦃ pres< it ⦄  ≈˘⟨ ≡⇒≃ conti ⟩
    G (lim f)                 ∎ where open CrossTreeReasoning
```

```agda
Func↾ : Ord → Set
Func↾ i = (x : Ord) → ⦃ i≤ : i ≤ x ⦄ → Ord
```

```agda
inflates-from-syntax : (i : Ord) → Func↾ i → Rel → Set
inflates-from-syntax i F _~_ = ∀ {x} ⦃ i≤ : i ≤ x ⦄ → x ~ F x

preserves-from-syntax : (i : Ord) → Func↾ i → Rel → Set
preserves-from-syntax i F _~_ = ∀ {x y} ⦃ i≤₁ : i ≤ x ⦄ ⦃ i≤₂ : i ≤ y ⦄ → x ~ y → F x ~ F y

syntax inflates-from-syntax i F _~_ = F inflates _~_ from i
syntax preserves-from-syntax i F _~_ = F preserves _~_ from i
```

```agda
record Iterable : Set where
  constructor iterable
  field
    init : Ord
    _[_] : Func↾ init
    infl< : _[_] inflates _<_ from init
variable ℱ : Iterable
```

```agda
open Iterable public
open Normal public
```

```agda
_^⟨_⟩_ : (ℱ : Iterable) → Ord → Func↾ (init ℱ)
^⟨⟩◌-infl≤ : (_^⟨_⟩_ ℱ a) inflates _≤_ from (init ℱ)
^⟨◌⟩-pres< : ⦃ _ : init ℱ ≤ i ⦄ → (ℱ ^⟨_⟩ i) preserves _<_
```

```agda
init≤ : ⦃ _ : init ℱ ≤ i ⦄ → init ℱ ≤ ℱ ^⟨ a ⟩ i
init≤ {ℱ} {i} {a} =                       begin
  init ℱ                                  ≤⟨ it ⟩
  i                                       ≤⟨ ^⟨⟩◌-infl≤ ⟩
  ℱ ^⟨ a ⟩ i                              ∎ where open SubTreeReasoning
```

```agda
ℱ ^⟨ zero ⟩ i = i
ℱ ^⟨ suc a ⟩ i = (ℱ [ ℱ ^⟨ a ⟩ i ]) ⦃ init≤ ⦄
ℱ ^⟨ lim f ⟩ i = lim (λ n → ℱ ^⟨ f n ⟩ i) ⦃ ^⟨◌⟩-pres< it ⦄
```

```agda
^⟨⟩◌-infl≤ {a = zero} = inj₂ refl
^⟨⟩◌-infl≤ {a = suc a} {ℱ} {x} =          begin
  x                                       ≤⟨ ^⟨⟩◌-infl≤ ⟩
  ℱ ^⟨ a ⟩ x                              ≤⟨ <⇒≤ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc a ⟩ x                          ∎ where open SubTreeReasoning
^⟨⟩◌-infl≤ {a = lim f} {ℱ} {x} =          begin
  x                                       ≤⟨ ^⟨⟩◌-infl≤ ⟩
  ℱ ^⟨ f 0 ⟩ x                            <⟨ <lim₂ ⦃ ^⟨◌⟩-pres< it ⦄ (^⟨◌⟩-pres< it) ⟩
  ℱ ^⟨ lim f ⟩ x                          ∎ where open SubTreeReasoning
```

```agda
^⟨◌⟩-pres< {ℱ} {i} {x} <suc =              begin-strict
  ℱ ^⟨ x ⟩ i                              <⟨ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc x ⟩ i                          ∎ where open SubTreeReasoning
^⟨◌⟩-pres< {ℱ} {i} {x} (<suc₂ {b} p) =     begin-strict
  ℱ ^⟨ x ⟩ i                              <⟨ ^⟨◌⟩-pres< p ⟩
  ℱ ^⟨ b ⟩ i                              <⟨ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc b ⟩ i                          ∎ where open SubTreeReasoning
^⟨◌⟩-pres< {ℱ} {i} (<lim {f} {n}) =        begin-strict
  ℱ ^⟨ f n ⟩ i                            <⟨ <lim ⦃ ^⟨◌⟩-pres< it ⦄ ⟩
  ℱ ^⟨ lim f ⟩ i                          ∎ where open SubTreeReasoning
^⟨◌⟩-pres< {ℱ} {i} {x} (<lim₂ {f} {n} p) = begin-strict
  ℱ ^⟨ x ⟩ i                              <⟨ ^⟨◌⟩-pres< p ⟩
  ℱ ^⟨ f n ⟩ i                            <⟨ <lim₂ ⦃ ^⟨◌⟩-pres< it ⦄ (^⟨◌⟩-pres< it) ⟩
  ℱ ^⟨ lim f ⟩ i                          ∎ where open SubTreeReasoning
```

```agda
^⟨◌⟩-pres≤ : ⦃ _ : init ℱ ≤ i ⦄ → (ℱ ^⟨_⟩ i) preserves _≤_
^⟨◌⟩-pres≤ = pres<→pres≤ ^⟨◌⟩-pres<
```

```agda
^⟨⟩◌-infl< : ⦃ NonZero a ⦄ → (_^⟨_⟩_ ℱ a) inflates _<_ from (init ℱ)
^⟨⟩◌-infl< {suc a} {ℱ} {x} =              begin-strict
  x                                       ≤⟨ ^⟨⟩◌-infl≤ ⟩
  ℱ ^⟨ a ⟩ x                              <⟨ ^⟨◌⟩-pres< <suc ⟩
  ℱ ^⟨ suc a ⟩ x                          ∎ where open SubTreeReasoning
^⟨⟩◌-infl< {lim f} {ℱ} {x} =              begin-strict
  x                                       <⟨ ^⟨⟩◌-infl< ⦃ fs-nz f ⦄ ⟩
  ℱ ^⟨ f 1 ⟩ x                            <⟨ ^⟨◌⟩-pres< <lim ⟩
  ℱ ^⟨ lim f ⟩ x                          ∎ where open SubTreeReasoning
```

```agda
_^⟨_⟩ : (ℱ : Iterable) (a : Ord) → ⦃ NonZero a ⦄ → Iterable
_^⟨_⟩ ℱ a = iterable (init ℱ) (_^⟨_⟩_ ℱ a) ^⟨⟩◌-infl<
```

```agda
_⟨_⟩^ : (ℱ : Iterable) (i : Ord ) → ⦃ init ℱ ≤ i ⦄ → Normal
ℱ ⟨ i ⟩^ = normal (ℱ ^⟨_⟩ i) ^⟨◌⟩-pres< refl
```

```agda
^⟨◌⟩-incr≼ : ⦃ _ : init ℱ ≤ i ⦄ → (ℱ ^⟨_⟩ i) inflates _≼_
^⟨◌⟩-incr≼ {x = zero} = z≼
^⟨◌⟩-incr≼ {ℱ} {i} {suc x} =              begin
  suc x                                   ≤⟨ s≼s ^⟨◌⟩-incr≼ ⟩
  suc (ℱ ^⟨ x ⟩ i)                        ≤⟨ <⇒≺ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc x ⟩ i                          ∎ where open CrossTreeReasoning
^⟨◌⟩-incr≼ {ℱ} {i} {lim f} = l≼ $         begin
  f _                                     ≤⟨ ≼l ⦃ ^⟨◌⟩-pres< it ⦄ ^⟨◌⟩-incr≼ ⟩
  ℱ ^⟨ lim f ⟩ i                          ∎ where open CrossTreeReasoning
```

```agda
^⟨⟩◌-pres≼ : (ℱ [_]) preserves _≼_ from (init ℱ) → (_^⟨_⟩_ ℱ a) preserves _≼_ from (init ℱ)
^⟨⟩◌-pres≼ {a = zero} _ = id
^⟨⟩◌-pres≼ {a = suc a} pres≼ p = pres≼ ⦃ init≤ ⦄ ⦃ init≤ ⦄ (^⟨⟩◌-pres≼ pres≼ p)
^⟨⟩◌-pres≼ {a = lim f} pres≼ p = l≼l ⦃ ^⟨◌⟩-pres< it ⦄ ⦃ ^⟨◌⟩-pres< it ⦄ (^⟨⟩◌-pres≼ pres≼ p)
```

```agda
^⟨◌⟩-pres∸≼ : ⦃ _ : init ℱ ≤ i ⦄ → ℱ ^⟨ suc (a ∸ δ) ⟩ i ≼ ℱ ^⟨ a ⟩ i
^⟨◌⟩-pres∸≼ {ℱ} {i} {suc a} {inj₁ tt} = ≼-refl
^⟨◌⟩-pres∸≼ {ℱ} {i} {suc a} {inj₂ δ } =   begin
  ℱ ^⟨ suc (a ∸ δ) ⟩ i                    ≤⟨ ^⟨◌⟩-pres∸≼ ⟩
  ℱ ^⟨ a ⟩ i                              ≤⟨ ≤⇒≼ $ <⇒≤ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc a ⟩ i                          ∎ where open CrossTreeReasoning
^⟨◌⟩-pres∸≼ {ℱ} {i} {lim f} {n , δ} =     begin
  ℱ ^⟨ suc (f n ∸ δ) ⟩ i                  ≤⟨ ^⟨◌⟩-pres∸≼ ⟩
  ℱ ^⟨ f n ⟩ i                            ≤⟨ ≼l ⦃ ^⟨◌⟩-pres< it ⦄ ≼-refl ⟩
  ℱ ^⟨ lim f ⟩ i                          ∎ where open CrossTreeReasoning
```

```agda
^⟨◌⟩-pres≼ : ⦃ _ : init ℱ ≤ i ⦄ → (ℱ [_]) preserves _≼_ from (init ℱ) → (ℱ ^⟨_⟩ i) preserves _≼_
^⟨◌⟩-pres≼ {ℱ} {i} pres≼ {x} {y} z≼ = ≤⇒≼ ^⟨⟩◌-infl≤
^⟨◌⟩-pres≼ {ℱ} {i} pres≼ {x} {y} (s≼ p) = begin
  ℱ ^⟨ x ⟩ i                              ≤⟨ pres≼ ⦃ init≤ ⦄ ⦃ init≤ ⦄ (^⟨◌⟩-pres≼ pres≼ p) ⟩
  ℱ ^⟨ suc (y ∸ _) ⟩ i                    ≤⟨ ^⟨◌⟩-pres∸≼ ⟩
  ℱ ^⟨ y ⟩ i                              ∎ where open CrossTreeReasoning
^⟨◌⟩-pres≼ {ℱ} {i} pres≼ {lim f} {y} (l≼ p) = l≼ ⦃ ^⟨◌⟩-pres< it ⦄ $ begin
  ℱ ^⟨ f _ ⟩ i                            ≤⟨ ^⟨◌⟩-pres≼ pres≼ p ⟩
  ℱ ^⟨ y ⟩ i                              ∎ where open CrossTreeReasoning
```

```agda
^⟨◌⟩-pres≺ : ⦃ _ : init ℱ ≤ i ⦄ → (ℱ [_]) preserves _≼_ from (init ℱ) → (ℱ ^⟨_⟩ i) preserves _≺_
^⟨◌⟩-pres≺ {ℱ} {i} pres≼ {x} {(zero)} (s≼ {δ = ()} _)
^⟨◌⟩-pres≺ {ℱ} {i} pres≼ {x} {suc y} p =  begin-strict
  ℱ ^⟨ x ⟩ i                              ≤⟨ ^⟨◌⟩-pres≼ pres≼ (s≼s-inj p) ⟩
  ℱ ^⟨ y ⟩ i                              <⟨ <⇒≺ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc y ⟩ i                          ∎ where open CrossTreeReasoning
^⟨◌⟩-pres≺ {(ℱ)} {(i)} pres≼ {(x)} {lim f} (s≼ p) = begin-strict
  ℱ ^⟨ x ⟩ i                              ≤⟨ ^⟨◌⟩-pres≼ pres≼ p ⟩
  ℱ ^⟨ f _ ∸ _ ⟩ i                        <⟨ <⇒≺ $ infl< ℱ ⦃ init≤ ⦄ ⟩
  ℱ ^⟨ suc (f _ ∸ _) ⟩ i                  ≤⟨ ^⟨◌⟩-pres∸≼ ⟩
  ℱ ^⟨ f _ ⟩ i                            ≤⟨ f≼l ⦃ ^⟨◌⟩-pres< it ⦄ ⟩
  ℱ ^⟨ lim f ⟩ i                          ∎ where open CrossTreeReasoning
```

可迭代函数迭代后的性质汇总

|        | 迭代次数               | 初值 |
| ----   | ----                  | ---- |
| pres < |   ✓                   |  ✗   |
| pres ≤ |   ✓                   |  ✗   |
| infl < |   ✗                   |  ✓ (NonZero) |
| infl ≤ |   ✗                   |  ✓   |
| normal |   ✓                   |  ✗   |
| pres ≺ |   ✓ (pres ≼)          |  ✗   |
| pres ≼ |   ✓ (pres ≼)          |  ✓ (pres ≼) |
| infl ≺ |   ✗                   |  ✓ (NonZero) |
| infl ≼ |   ✓ (pres ≼)          |  ✓   |
