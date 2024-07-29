---
title: 形式化大数数学 (2.0 - 良构树序数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.0 - 良构树序数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/WellFormed.Base.html)  

本系列文章致力于可运行且保证停机的大数计算程序的文学编程. 我们在[第一章](https://zhuanlan.zhihu.com/p/707713300)定义出了 [LVO](https://googology.fandom.com/wiki/Large_Veblen_ordinal), 接下来计划介绍[序数崩塌函数 (OCF)](https://googology.fandom.com/wiki/Ordinal_collapsing_function).
如果希望用这套方法走得比较远的话 (比如达到 [EBO](https://googology.fandom.com/wiki/Extended_Buchholz's_function)), 那么对基础理论有较高的要求. 我们需要从底层定义开始, 把严格性再提高一个档次, 因此会先花费相当大的篇幅构建良构树序数相关的理论.

## 基础的选取

我们发现对于 EBO 的定义, [函数外延性](https://ncatlab.org/nlab/show/function+extensionality), [证明无关性](https://ncatlab.org/nlab/show/proof+relevance)以及特定命题到集合的[大消去](https://cstheory.stackexchange.com/questions/40339/what-exactly-is-large-elimination)似乎是不可或缺的. 同伦类型论 (HoTT) 可以优雅地满足这三个需求, 因此我们采用它的一个Agda版本——立方类型论 (Cubical Agda) 作为数学基础. 采用 HoTT 作为基础的另一个好处是, [泛等原理](https://ncatlab.org/nlab/show/univalent+foundations+for+mathematics)将帮助我们省去一部分重复代码, 这在后篇可以看到.

```agda
{-# OPTIONS --safe --cubical #-}
module WellFormed.Base where
```

### 库依赖

我们采用[命题相等](https://ncatlab.org/nlab/show/propositional+equality)作为主要使用的[同一性概念](https://ncatlab.org/nlab/show/equality), 而[道路类型 (path type)](https://ncatlab.org/nlab/show/path+type) 只作为一个辅助. 在 HoTT 中这两者是等价的, 但分情况使用可以简化证明.

**Cubical库**

```agda
open import Cubical.Foundations.Prelude as 🧊 public
  hiding (_≡_; refl; sym; cong; cong₂; subst; _∎)
open import Cubical.Data.Equality public
  using (pathToEq; eqToPath; PathPathEq)
open import Cubical.Data.Sigma public
  using (Σ-syntax; _×_; _,_; fst; snd; ΣPathP)
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map; map2; rec→Set)
```

**标准库**

```agda
open import Data.Unit public using (⊤; tt)
open import Data.Nat as ℕ public using (ℕ; zero; suc)
open import Function public using (id; flip; _∘_; _$_; _∋_; it; case_of_)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; subst)
```

**桥接库**

用于处理Cubical库与标准库混用时的一些问题.

```agda
open import Bridged.Data.Empty public using (⊥; ⊥-elim; isProp⊥)
open import Bridged.Data.Sum public using (_⊎_; inl; inr; isProp⊎)
```

## 良构树序数

我们互归纳定义序数及其上的序关系, 因为我们的序数定义中就要用到由该序关系表达的一个条件作为约束. 这种约束后的序数我们称为良构树序数 $\text{Ord}$, 约束所用的序关系称为路径关系 $\text{Rd}(a, b)$, 其中 $a,b : \text{Ord}$. 这里所说的路径其实就是树 (tree) 中的路径 (path), 为了避免与 HoTT 中的道路 (path) 混淆, 我们称之为路径 (road). 后面会证明, $\text{Rd}(a, b)$ 是同伦层级意义下的集合, 也就是说 $\text{Rd}(a, b)$ 表示从序数 $a$ 到序数 $b$ 的所有路径所组成的集合.

```agda
data Ord : Type
data Road : Ord → Ord → Type
```

以上只是声明我们将要定义的东西, 它们的具体定义将在后面给出. 但在给出之前, 我们要假装它们已经完成了, 来表达定义中要用的一些辅助概念.

**定义 2-0-0** 我们说 $a$ 是 $b$ 的子树, 记作 $a \lt b$, 当且仅当存在一条从 $a$ 到 $b$ 的路径.

```agda
_<_ : Ord → Ord → Type; infix 6 _<_
a < b = ∥ Road a b ∥₁
```

注意此处说的「存在」形式表达为路径关系的命题截断, 满足

- 任给一条路径 $r:\text{Rd}(a,b)$, 都可以证明 $|r|:a\lt b$
- 任意两个证明 $p,q:a\lt b$ 都有 $p = q$

**定义 2-0-1** 我们将自然数到序数的函数简称**序列**, 其类型 $ℕ→\text{Ord}$ 简记为 $\text{Seq}$.

```agda
Seq : Type
Seq = ℕ → Ord
```

**定义 2-0-2** 我们说一个序列 $f:\text{Seq}$ 是**良构**的 (well-formed), 记作 $\text{wf}(f)$, 当且仅当它严格单调递增, 即对任意 $n$ 都有 $f(n) < f(n^+)$. 良构序列又叫序数的基本列.

```agda
wf : Seq → Type
wf f = ∀ {n} → f n < f (suc n)
```

**约定 2-0-3** 我们使用 $m,n$ 表示自然数, $a,b,c$ 表示序数, $f,g,h$ 表示基本列, $r,s,t$ 表示路径.

```agda
variable
  m n : ℕ
  a b c : Ord
  f g h : Seq
  r s t : Road a b
```

现在给出良构树序数和路径关系的具体定义.

**定义 2-0-4** 良构树序数

$$
\frac{}{\quad\text{zero} : \text{Ord}\quad}
\qquad
\frac{a:\text{Ord}}{\quad\text{suc}(a):\text{Ord}\quad}
\qquad
\frac{f:\text{Seq}\quad w : \text{wf}(f)}{\quad\lim(f,w):\text{Ord}\quad}
$$

后文在没有歧义的情况下采用如下简写:
- $\text{zero}$ 记作 $0$
- $\text{suc}(a)$ 记作 $a^+$
- $\lim(f,w)$ 记作 $\lim(f)$

```agda
data Ord where
  zero : Ord
  suc  : Ord → Ord
  lim  : (f : Seq) → ⦃ wf f ⦄ → Ord
```

**定义 2-0-5** 路径关系

$$
\frac{}
{\quad\text{zero} : \text{Rd}(a, a^+)\quad}
\qquad
\frac{r:\text{Rd}(a,b)}
{\quad\text{suc}(r):\text{Rd}(a,b^+)\quad}
\qquad
\frac{\quad f:\text{Seq}\quad w:\text{wf}(f)\quad r:\text{Rd}(a,f(n))\quad}
{\lim(f,w,r):\text{Rd}(a,\lim(f))}
$$

后文在没有歧义的情况下采用如下简写:
- $\text{zero}$ 记作 $0$
- $\text{suc}(r)$ 记作 $r^+$
- $\lim(f,w,r)$ 记作 $\lim(r)$

```agda
data Road where
  zero : Road a (suc a)
  suc  : Road a b → Road a (suc b)
  lim  : ⦃ _ : wf f ⦄ → Road a (f n) → Road a (lim f)
```

注意此处序数与路径的记法是重载的 (overloaded), 从上下文可以推断它们指的是序数的概念还是路径的概念.

**约定 2-0-6** 对于路径关系的截断——子树关系, 我们还将采用如下简写:

- $|0|$ 记作 $0_1$
- $|r^+|$ 记作 $r^{+_1}$
- $|\lim(r)|$ 记作 $\lim_1(r)$

```agda
pattern zero₁  = ∣ zero ∣₁
pattern suc₁ r = ∣ suc r ∣₁
pattern lim₁ r = ∣ lim r ∣₁
```

### 基本性质

**事实 2-0-7** 良构条件是命题. 这意味着它们对极限序数的同一性没有影响.

```agda
isPropWf : isProp (wf f)
isPropWf = isPropImplicitΠ λ _ → squash₁
  where open import Cubical.Foundations.HLevels
```

由该事实, 结合 HoTT 承诺的函数外延性可得

**事实 2-0-8** 两个良构序列的极限相等, 只要它们逐项相等.

```agda
limExtPath : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → Path _ (f n) (g n)) → Path Ord (lim f) (lim g)
limExtPath p = 🧊.cong₂ (λ f (wff : wf f) → Ord.lim f ⦃ wff ⦄) (funExt p) (toPathP $ isPropWf _ _)

limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → (∀ n → f n ≡ g n) → lim f ≡ lim g
limExt p = pathToEq $ limExtPath $ eqToPath ∘ p
```

## 序数集合

```agda
module OrdSet where
  open import Cubical.Foundations.HLevels
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
    (decodeEncode a b) (isPropCover a b)

  isProp≡ : isProp (a ≡ b)
  isProp≡ = 🧊.subst isProp PathPathEq (isSetOrd _ _)
```

**事实 2-0-9** 序数类型是集合, 也即序数的同一性是命题.

```agda
open OrdSet public using (isSetOrd; isProp≡)
```

## 路径与子树关系

接下来我们考察路径关系及其截断——子树关系. 我们追加导入标准库中关于自然数的引理, 以及序关系的相关概念, 如什么是严格偏序, 什么是非严格偏序等.

```agda
import Data.Nat.Properties as ℕ
open import Relation.Binary.Definitions
open import Relation.Binary.Structures {A = Ord} _≡_
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded
```

### 严格序

**事实 2-0-10** 路径关系与子树关系尊重命题相等, 即

- 如果 $\text{Rd}(a,b)$ 且 $a=c$ 那么 $\text{Rd}(c,b)$
- 如果 $\text{Rd}(a,b)$ 且 $b=c$ 那么 $\text{Rd}(a,c)$
- 如果 $a \lt b$ 且 $a=c$ 那么 $c \lt b$
- 如果 $a \lt b$ 且 $b=c$ 那么 $a \lt c$


```agda
rd-resp-≡ : Road Respects₂ _≡_
rd-resp-≡ = (λ { refl → id }) , (λ { refl → id })

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

**定义 2-0-11** 任给 $r:\text{Rd}(a, b)$ 以及 $s:\text{Rd}(b, c)$, 递归定义**路径的结合** $r⋅s : \text{Rd}(a, c)$ 如下

- 若 $s=0$, 必然有 $c=b^+$, 于是 $r⋅s := r^+:\text{Rd}(a,b^+)$.
- 若存在 $s'$ 使得 $s=s'^+$, 必然存在 $c'$ 使得 $c=c'^+$ 且 $s':\text{Rd}(b,c')$, 于是 $r⋅s := (r⋅s')^+:\text{Rd}(a,c'^+)$.
- 若存在 $s'$ 使得 $s=\lim(s')$, 必然存在 $f$ 使得 $c=\lim(f)$ 且 $s':\text{Rd}(a,f(n))$, 于是 $r⋅s := \lim(r⋅s'):\text{Rd}(a,\lim(f))$. ∎

```agda
rd-trans : Transitive Road
rd-trans r zero    = suc r
rd-trans r (suc s) = suc (rd-trans r s)
rd-trans r (lim s) = lim (rd-trans r s)
```

**事实 2-0-12** 由路径的结合立即可得子树关系的传递性.

```agda
<-trans : Transitive _<_
<-trans = map2 rd-trans
```

**定理 2-0-13** 路径关系是良基关系, 即任意序数 $a$ 在路径关系下可及.  
**证明** 在我们这套定义下, 该定理有一个技巧性的简短证明. 我们先假设存在 $a$ 到某 $b$ 的路径 $r:\text{Rd}(a,b)$, 以此证明 $a$ 可及之后, 提供 $0:\text{Rd}(a,a^+)$ 消掉此前提. 现在, 假设有这样的 $r$, 对 $r$ 归纳.

- 若 $r=0$, 要证 $a$ 在路径关系下可及, 即证任意满足 $s:\text{Rd}(c,a)$ 的 $c$ 可及, 此即归纳假设.
- 若存在 $r'$ 使得 $r=r'^+$, 必然存在 $b'$ 使得 $b=b'^+$ 且 $r':\text{Rd}(a,b')$. 现在要证 $a$, 即证任意满足 $s:\text{Rd}(c,a)$ 的 $c$ 可及. 由归纳假设, 只需找到某 $x$ 满足 $\text{Rd}(c,x)$. 令 $x=b'$, 我们有 $s⋅r':\text{Rd}(c,b')$.
- 同理可证 $r=\lim(r')$ 的情况. ∎

```agda
rd-acc : Road a b → Acc Road a
rd-acc zero    = acc λ s → rd-acc s
rd-acc (suc r) = acc λ s → rd-acc (rd-trans s r)
rd-acc (lim r) = acc λ s → rd-acc (rd-trans s r)

rd-wellFounded : WellFounded Road
rd-wellFounded _ = rd-acc zero
```

**定理 2-0-14** 子树关系是良基关系.  
**证明** 与路径关系的证明类似, 但需要先证明命题关系的可及性是命题, 暴露出立方类型论的区间原语 `i` 后归纳即得. ∎

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

**推论 2-0-15** 路径关系和子树关系都是非对称且反自反的.  
**证明** 良基关系都是非对称且反自反的. ∎

```agda
rd-asym : Asymmetric Road
rd-asym = wf⇒asym rd-wellFounded

rd-irrefl : Irreflexive _≡_ Road
rd-irrefl = wf⇒irrefl rd-resp-≡ sym rd-wellFounded

<-asym : Asymmetric _<_
<-asym = wf⇒asym <-wellFounded

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = wf⇒irrefl <-resp-≡ sym <-wellFounded
```

**定理 2-0-16** 路径关系与子树关系分别构成严格偏序.  
**证明** 由以上讨论可知. ∎

```agda
rd-isStrictPartialOrder : IsStrictPartialOrder Road
rd-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = rd-irrefl
  ; trans = rd-trans
  ; <-resp-≈ = rd-resp-≡ }

<-isStrictPartialOrder : IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl = <-irrefl
  ; trans = <-trans
  ; <-resp-≈ = <-resp-≡ }
```

### 非严格序

**定义 2-0-17** 非严格序

- 序数 $a$ 到 $b$ 的非严格路径, 记作 $\widetilde{\text{Rd}}(a,b)$, 定义为和类型 $\text{Rd}(a,b)+(a=b)$.
- 非严格子树关系, 记作 $a \le b$, 定义为和类型 $(a < b) + (a = b)$.

```agda
open import Relation.Binary.Construct.StrictToNonStrict _≡_ Road
  as NonStrictRoad public using () renaming (_≤_ to infix 6 NSRoad; <⇒≤ to rd→ns)

open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_
  as NonStrictSubTree public using () renaming (_≤_ to infix 6 _≤_; <⇒≤ to <→≤)
```

**事实 2-0-18** 给定非严格路径, 可以证明非严格子树关系.

```agda
ns→≤ : NSRoad a b → a ≤ b
ns→≤ (inl r) = inl ∣ r ∣₁
ns→≤ (inr p) = inr p
```

**引理 2-0-19** 非严格子树关系也是命题.  
**引理** 如果和类型两边的命题互斥, 那么和类型也是一个命题. 由 $\lt$ 的反自反性, 显然 $a \lt b$ 与 $a = b$ 互斥. ∎

```agda
isProp≤ : isProp (a ≤ b)
isProp≤ = isProp⊎ squash₁ isProp≡ (flip <-irrefl)
```

**定理 2-0-20** $a$ 到 $b^+$ 的严格路径可以转换为 $a$ 到 $b$ 的非严格路径.  
**证明** 讨论 $r:\text{Rd}(a,b^+)$.
- 若 $r=0$, 则必然有 $a=b$.
- 若存在 $r'$ 使得 $r=r'^+$, 则必然有 $r':\text{Rd}(a,b)$. ∎

```agda
rds→ns : Road a (suc b) → NSRoad a b
rds→ns zero    = inr refl
rds→ns (suc r) = inl r
```

**推论 2-0-21** 如果 $a \lt b^+$, 那么 $a \le b$.  
**证明** 由上述定理及引理 2-0-19 ($\le$ 的命题性) 即得. ∎

```agda
<s→≤ : a < suc b → a ≤ b
<s→≤ = rec isProp≤ (ns→≤ ∘ rds→ns)
```

**事实 2-0-22** 定理 2-0-20 以及推论 2-0-21 的逆命题也成立.  
**证明** 讨论和类型的两边即可. ∎

```agda
ns→rds : NSRoad a b → Road a (suc b)
ns→rds (inl r)    = suc r
ns→rds (inr refl) = zero

≤→<s : a ≤ b → a < suc b
≤→<s (inl r)    = map suc r
≤→<s (inr refl) = zero₁
```

**定理 2-0-23** 非严格路径关系和非严格子树关系分别满足自反性, 反对称性和传递性.  
**证明** 由定义显然. ∎

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

**定理 2-0-24** 非严格路径关系与非严格子树关系分别构成非严格偏序.  
**证明** 由以上讨论可知. ∎

```agda
ns-isPreorder : IsPreorder NSRoad
ns-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inr
  ; trans = ns-trans
  }

ns-isPartialOrder : IsPartialOrder NSRoad
ns-isPartialOrder = record { isPreorder = ns-isPreorder ; antisym = ns-antisym }

≤-isPreorder : IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = inr
  ; trans = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≤_
≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }
```

证明以上性质后, 我们可以实例化以下记法模块以提高序关系证明代码的可读性, 会在后文中看到.

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

**引理 2-0-25** 良构序列 $f$ 保持自然数的序, 即对任意 $m < n$ 都有 $f(m) < f(n)$.  
**证明** 对 $n$ 归纳.

- 若 $n=0$, 虚空真.
- 若 $n=n'^+$, 有 $m\lt n'^+$, 即 $m≤n'$
  - 若 $m\lt n'$, 由归纳假设有 $f(m)\lt f(n')$, 由 $f$ 的良构性质有 $f(n')\lt f(n'^+)$, 由 $\lt$ 的传递性有 $f(m)\lt f(n'^+)=f(n)$.
  - 若 $m=n'$, 由 $f$ 的良构性质有 $f(m)=f(n')\lt f(n'^+)=f(n)$. ∎

```agda
seq-pres< : ⦃ _ : wf f ⦄ → m ℕ.< n → f m < f n
seq-pres< {f} {m} (ℕ.s≤s {n} m≤n) with ℕ.m≤n⇒m<n∨m≡n m≤n
... | inl m<n = begin-strict
  (f m)         <⟨ seq-pres< m<n ⟩
  (f n)         <⟨ it ⟩
  f (suc n)     ∎ where open SubTreeReasoning
... | inr refl = it
```

注意上面的代码用到了我们之前提到的高可读记法, 我们称为序关系推理链.

**引理 2-0-26** 良构序列对自然数的相等单射, 即如果序列的两个项相等, 那么它们的序号相等.  
**证明** 由良构序列的严格递增性显然成立. ∎

```agda
seq-inj≡ : ∀ f → ⦃ _ : wf f ⦄ → f m ≡ f n → m ≡ n
seq-inj≡ {m} {n} _ eq with ℕ.<-cmp m n
... | tri< m<n _ _  = ⊥-elim $ <-irrefl eq (seq-pres< m<n)
... | tri≈ _ refl _ = refl
... | tri> _ _ n<m  = ⊥-elim $ <-irrefl (sym eq) (seq-pres< n<m)
```

**引理 2-0-27** 良构序列反映自然数的序, 即序列的两个项的大小关系反映序号的大小关系.  
**证明** 由良构序列的严格递增性显然成立. ∎

```agda
seq-inj< : ∀ f → ⦃ _ : wf f ⦄ → f m < f n → m ℕ.< n
seq-inj< {m} {n} _ r with ℕ.<-cmp m n
... | tri< m<n _ _  = m<n
... | tri≈ _ refl _ = ⊥-elim $ <-irrefl refl r
... | tri> _ _ n<m  = ⊥-elim $ <-asym r (seq-pres< n<m)
```

**事实 2-0-28** 对良构序列 $f$, 不存在 $m$ 使得 $f(m)$ 正好位于 $f(n)$ 与 $f(n^+)$ 之间.  
**证明** 由引理 2-0-25 以及自然数的相关性质可得. ∎

```agda
seq-notDense : ∀ f → ⦃ _ : wf f ⦄ → f n < f m → f m < f (suc n) → ⊥
seq-notDense f r s = ℕ.<⇒≱ (seq-inj< f r) (ℕ.m<1+n⇒m≤n (seq-inj< f s))
```

## 同株关系

**定义 2-0-29** 序数 $a$ 与 $b$ 同株集, 记作 $\text{Homo}(a,b)$, 定义为从 $a$ 与 $b$ 通过路径关系共同延伸出去的那些序数. 如果该同株集非空, 我们就说 $a$ 与 $b$ 同株.

```agda
Homo : Ord → Ord → Type
Homo a b = Σ[ c ∈ Ord ] Road a c × Road b c
```

**事实 2-0-30** 同株关系是自反且对称的.  
**证明** 由定义显然. ∎

```agda
Homo-refl : Reflexive Homo
Homo-refl {x} = suc x , zero , zero

Homo-sym : Symmetric Homo
Homo-sym (c , a<c , b<c) = c , b<c , a<c
```

**注意 2-0-31** 同株关系不是传递关系. 比如 $0$ 与 $\lim(0,1,...)$ 同株, 也与 $\lim(1,2,...)$ 同株, 但后两者不同株. 「考虑同株」是在不商掉后两者的那种等价关系的情况下的代替处理方法, 出于形式上简洁的考虑.

## 子树的三歧性

**引理 2-0-32** 子树关系的连通性 $(a \lt b) + (b ≤ a)$ 是命题.  
**证明** 由推论 2-0-15 ($\lt$ 的反自反性), $a\lt b$ 与 $b≤a$ 互斥. ∎

```agda
isPropConnex : isProp (a < b ⊎ b ≤ a)
isPropConnex = isProp⊎ squash₁ isProp≤ λ r s → <-irrefl refl (<-≤-trans r s)
```

**引理 2-0-33** 忽略非同株序数 (up to homo), $\lt$ 与 $≤$ 连通.

```agda
<-connex-homo : Road a c → Road b c → a < b ⊎ b ≤ a
<-connex-homo zero    zero    = inr $ inr refl
<-connex-homo zero    (suc s) = inr $ inl ∣ s ∣₁
<-connex-homo (suc r) zero    = inl ∣ r ∣₁
<-connex-homo (suc r) (suc s) = <-connex-homo r s
<-connex-homo (lim {n} r) (lim {n = m} s) with ℕ.<-cmp n m
... | tri< n<m _ _  = rec isPropConnex (λ t → <-connex-homo (rd-trans r t) s) (seq-pres< n<m)
... | tri≈ _ refl _ = <-connex-homo r s
... | tri> _ _ m<n  = rec isPropConnex (λ t → <-connex-homo r (rd-trans s t)) (seq-pres< m<n)
```

```agda
<-connex : a < c → b < c → a < b ⊎ b ≤ a
<-connex = rec2 isPropConnex <-connex-homo
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
  open import Cubical.Axiom.UniquenessOfIdentity
  open import Cubical.Data.Nat using (discreteℕ; isSetℕ)
  open import Cubical.Relation.Nullary
```

```agda
  zero-unique : (r : Road a (suc a)) → Path _ r zero
  zero-unique r = aux r 🧊.refl where
    aux : (r : Road a (suc b)) (p : Path _ b a)
      → PathP (λ i → Road a (suc (p i))) r zero
    aux zero = UIP→AxiomK (isSet→UIP isSetOrd) _ _ _ 🧊.refl
    aux (suc r) p = ⊥-elim $ rd-irrefl (sym $ pathToEq p) r
```

```agda
  suc-inj : suc r ≡ suc s → r ≡ s
  suc-inj refl = refl

  suc-injPath : Path _ (suc r) (suc s) → Path _ r s
  suc-injPath = eqToPath ∘ suc-inj ∘ pathToEq
```

```agda
  lim-injPath : ⦃ _ : wf f ⦄ {r s : Road a (f n)} → Path (Road a (lim f)) (lim r) (lim s) → Path _ r s
  lim-injPath p = aux (pathToEq p) 🧊.refl where
    aux : ⦃ _ : wf f ⦄ {r : Road a (f n)} {s : Road a (f m)} → Road.lim {f = f} r ≡ lim s
      → (p : Path _ n m) → PathP (λ i → Road a (f (p i))) r s
    aux {f} {a} {r} {s} refl = UIP→AxiomK (isSet→UIP isSetℕ) _ _
      (λ p → PathP (λ i → Road a (f (p i))) r s) 🧊.refl
```

```agda
  discreteRoad : Discrete (Road a b)
  discreteRoad r zero           = yes (zero-unique r)
  discreteRoad zero (suc r)     = ⊥-elim (rd-irrefl refl r)
  discreteRoad (suc r) (suc s)  = mapDec (🧊.cong suc) (λ p q → p (suc-injPath q)) (discreteRoad r s)
  discreteRoad (lim {n = n₁} r) (lim {n = n₂} s) with discreteℕ n₁ n₂
  ... | yes p = case pathToEq p of λ { refl → mapDec (🧊.cong lim) (λ p q → p (lim-injPath q)) (discreteRoad r s) }
  ... | no p = no λ q → case pathToEq q of λ { refl → p 🧊.refl }
```

```agda
  isSetRoad : isSet (Road a b)
  isSetRoad = Discrete→isSet discreteRoad
```

```agda
open RoadSet public using (discreteRoad; isSetRoad)
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
  cano-2const zero    r       = case pathToEq (RoadSet.zero-unique r) of λ { refl → 🧊.refl }
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

一旦建立子树关系到路径关系的消去, 我们可以构造之前无法构造的路径.

```agda
f<l : ⦃ _ : wf f ⦄ → f n < lim f
f<l = map lim it
```

```agda
rd-f-l : ⦃ _ : wf f ⦄ → Road (f n) (lim f)
rd-f-l = <-largeElim f<l
```

子树的三歧性可以强化为路径的三歧性.

```agda
rd-trich : Road a c → Road b c → Tri (Road a b) (a ≡ b) (Road b a)
rd-trich r s with <-trich ∣ r ∣₁ ∣ s ∣₁
... | tri< t ¬u ¬v = tri< (<-largeElim t) ¬u  (¬v ∘ ∣_∣₁)
... | tri≈ ¬t u ¬v = tri≈ (¬t ∘ ∣_∣₁)     u   (¬v ∘ ∣_∣₁)
... | tri> ¬t ¬u v = tri> (¬t ∘ ∣_∣₁)     ¬u  (<-largeElim v)
```
