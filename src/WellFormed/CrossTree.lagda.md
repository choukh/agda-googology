---
title: 形式化大数数学 (2.3 - 跨树关系)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.3 - 跨树关系)

> 交流Q群: 893531731  
> 本文源码: [CrossTree.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/CrossTree.lagda.md)  
> 高亮渲染: [CrossTree.html](https://choukh.github.io/agda-googology/WellFormed.CrossTree.html)  

[上一篇](https://zhuanlan.zhihu.com/p/715504174)我们定义了序数的加法, 乘法和幂运算. 为了进一步研究序数运算的性质, 我们追加定义一种更宽泛的序关系, 它允许非同株树序数间建立关系, 我们称之为跨树关系. 本文将讨论跨树关系的性质, 并证明序数运算在跨树关系下的性质.

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.CrossTree where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic

open import Relation.Binary.Definitions
open import Induction.WellFounded
```

## 非严格序

**定义 2-3-0** 归纳定义非严格跨树关系 $a ≼ b$.

$$
\frac{}
{\quad\text{z≼} : 0 ≼ a\quad}
\qquad
\frac{a ≼ b}
{\quad\text{s≼s} : a^+ ≼ b^+\quad}
$$

$$
\frac{a ≼ f(n)}
{\quad\text{≼l} : a ≼ \lim(f)\quad}
\qquad
\frac{∀n, f(n) ≼ a}
{\quad\text{l≼} : \lim(f) ≼ a\quad}
$$

其中 $\text{s≼s}$ 说后继运算保持 $≼$, $\text{≼l}$ 说极限是基本列的上界, $\text{l≼}$ 说极限是基本列的上确界.

```agda
infix 6 _≼_
data _≼_ : Rel where
  z≼  : 0 ≼ a
  s≼s : a ≼ b → suc a ≼ suc b
  ≼l  : {w : wf f} → a ≼ f n → a ≼ lim f ⦃ w ⦄
  l≼  : {w : wf f} → (∀ {n} → f n ≼ a) → lim f ⦃ w ⦄ ≼ a
```

**事实 2-3-1** 后继运算单射 $≼$.  
**证明** 由归纳定义反演即得. ∎

```agda
s≼s-inj : suc injects _≼_
s≼s-inj (s≼s p) = p
```

**事实 2-3-2** $\text{l≼l}$ : 如果两个基本列逐项满足 $≼$, 那么它们的极限也满足 $≼$.  
**证明** 复合构造子 $\text{l≼}$ 与 $\text{≼l}$ 即得. ∎

```agda
l≼l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≼ g n) → lim f ⦃ wff ⦄ ≼ lim g ⦃ wfg ⦄
l≼l p = l≼ (≼l p)
```

**事实 2-3-3** 如果两个基本列错开一项后逐项满足 $≼$, 那么它们的极限也满足 $≼$.  
**证明** 复合构造子 $\text{l≼}$ 与 $\text{≼l}$ 并调整 $\text{≼l}$ 的参数即得. ∎

```agda
l≼ls : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≼ g (suc n)) → lim f ⦃ wff ⦄ ≼ lim g ⦃ wfg ⦄
l≼ls p = l≼ (λ {n} → (≼l {n = suc n} p))
```

**定理 2-3-4** $≼$ 是自反关系.  
**证明** 即证 $a ≼ a$, 对 $a$ 归纳. 零的情况用 $\text{z≼}$, 后继的情况用 $\text{s≼s}$ 和归纳假设, 极限的情况用 $\text{l≼l}$ 和归纳假设即得. ∎

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc x} = s≼s ≼-refl
≼-refl {lim f} = l≼l ≼-refl
```

**推论 2-3-5** 基本列的任一项都 $≼$ 其极限.  
**证明** 由 $\text{≼l}$ 配合 $≼$ 的自反性即得. ∎

```agda
f≼l : {w : wf f} → f n ≼ lim f ⦃ w ⦄
f≼l = ≼l ≼-refl
```

**定理 2-3-6** $≼$ 是传递关系.  
**证明** 要证 $p : a ≼ b$ 且 $q : b ≼ c$ 蕴含 $a ≼ c$. 同时对 $p,q$ 归纳, 分五种情况.

- 若 $p = \text{z≼} : 0 ≼ b$, 不管 $q$ 是什么, 都有 $\text{z≼} : 0 ≼ c$.
- 若 $p = \text{s≼s}(p') : a^+ ≼ b^+$, 且 $q = \text{s≼s}(q') : b^+ ≼ c^+$, 必有 $p' : a ≼ b$ 且 $q' : b ≼ c$, 由归纳假设得 $a ≼ c$, 再由 $\text{s≼s}$ 得 $a^+ ≼ c^+$.
- 不管 $p$ 是什么, 若 $q = \text{≼l}(q') : b ≼ \lim(f)$, 必有 $q' : b ≼ f(n)$, 要证 $a ≼ \lim(f)$. 由归纳假设得 $a ≼ f(n)$, 再由 $\text{≼l}$ 得 $a ≼ \lim(f)$.
- 不管 $q$ 是什么, 若 $p = \text{l≼}(p') : \lim(f) ≼ b$, 必有 $p' : ∀n, f(n) ≼ b$. 要证 $\lim(f) ≼ c$. 由归纳假设得 $∀n, f(n) ≼ c$, 再由 $\text{l≼}$ 得 $\lim(f) ≼ c$.
- 若 $p = \text{≼l}(p') : a ≼ \lim(f)$, 且 $q = \text{l≼}(q') : \lim(f) ≼ c$, 必有 $p' : a ≼ f(n)$ 且 $q' : ∀n, f(n) ≼ c$. 要证 $a ≼ c$. 由归纳假设即得. ∎

```agda
≼-trans : Transitive _≼_
≼-trans z≼      q       = z≼
≼-trans (s≼s p) (s≼s q) = s≼s (≼-trans p q)
≼-trans p       (≼l q)  = ≼l (≼-trans p q)
≼-trans (l≼ p)  q       = l≼ (≼-trans p q)
≼-trans (≼l p)  (l≼ q)  = ≼-trans p q
```

**推论 2-3-7** 构造子 $\text{l≼}$ 的反演: 如果 $\lim(f) ≼ a$, 那么 $∀n, f(n) ≼ a$.  
**证明** 讨论 $p : \lim(f) ≼ a$, 只可能有两种情况.

- 若 $p = \text{≼l}(p') : \lim(f) ≼ \lim(g)$, 必有 $p' : \lim(f) ≼ g(m)$. 要证 $∀n, f(n) ≼ \lim(g)$. 由传递性有 $∀n, f(n) ≼ \lim(f) ≼ g(m) ≼ \lim(g)$. ∎
- 若 $p = \text{l≼}(p') : \lim(f) ≼ a$, 必有 $p' : ∀n, f(n) ≼ a$. ∎

```agda
l≼-inv : {w : wf f} → lim f ⦃ w ⦄ ≼ a → f n ≼ a
l≼-inv (≼l p) = ≼-trans f≼l (≼l p)
l≼-inv (l≼ p) = p
```

**引理 2-3-8** 类似路径构造子, 对任意 $p : a ≼ b$ 有 $p^+ : a ≼ b^+$.  
**证明** 对 $p$ 归纳, 分四种情况.

- 若 $p = \text{z≼} : 0 ≼ b$, 有 $\text{z≼} : 0 ≼ b^+$.
- 若 $p = \text{s≼s}(p') : a^+ ≼ b^+$, 必有 $p' : a ≼ b$, 则 $\text{s≼s}(p'^+) : a^+ ≼ b^{++}$.
- 若 $p = \text{≼l}(p') : a ≼ \lim(f)$, 必有 $p' : a ≼ f(n)$, 则 $p'^+:a≼ f(n)^+$, 由传递性即得 $a≼\lim(f)^+$.
- 若 $p = \text{l≼}(p') : \lim(f) ≼ b$, 必有 $p' : ∀n, f(n) ≼ b$, 则 $p'^+ : ∀n, f(n) ≼ b^+$, 由 $\text{l≼}$ 即得 $\lim(f) ≼ b^+$. ∎

```agda
≼-suc : a ≼ b → a ≼ suc b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l p) = ≼-trans (≼-suc p) (s≼s f≼l)
≼-suc (l≼ p) = l≼ (≼-suc p)
```

**推论 2-3-9** 类似路径构造子, 有 $0 : a ≼ a^+$.  
**证明** 由引理 2-3-8 和 $≼$ 的自反性即得. ∎

```agda
≼-zero : a ≼ suc a
≼-zero = ≼-suc ≼-refl
```

**定理 2-3-10** 子树关系蕴含跨树关系: $a ≤ b → a ≼ b$.  
**证明** 归纳 r : a ≤ b$, 分四种情况.

- 若 $r = 0 : a < a^+$, 有 $0 : a ≼ a^+$.
- 若 $r = r'^+ : a < b^+$, 必有 $r' : a < b$, 由归纳假设有 $p : a ≼ b$, 所以 $p^+ : a ≼ b^+$.
- 若 $r = \lim(r') : a < \lim(f)$, 必有 $r' : a < f(n)$, 由归纳假设有 $p : a ≼ f(n)$, 所以 $\text{≼l}(p) : a ≼ \lim(f)$.
- 若 $r : a = b$, 由 $≼$ 的自反性即得. ∎

```agda
≤→≼-rd : NSRoad a b → a ≼ b
≤→≼-rd (inl zero) = ≼-zero
≤→≼-rd (inl (suc r)) = ≼-suc (≤→≼-rd (inl r))
≤→≼-rd (inl (lim r)) = ≼l (≤→≼-rd (inl r))
≤→≼-rd (inr refl) = ≼-refl

≤→≼ : a ≤ b → a ≼ b
≤→≼ (inl r) = ≤→≼-rd (inl (set r))
≤→≼ (inr refl) = ≼-refl
```

## 外延相等

**定义 2-3-11** 我们说 $a$ 与 $b$ 外延相等, 记作 $a ≈ b$, 但且仅当 $a ≼ b$ 且 $b ≼ a$.

```agda
_≈_ : Rel; infix 5 _≈_
a ≈ b = a ≼ b × b ≼ a
```

**事实 2-3-12** $≼$ 相对于 $≈$ 是反对称关系.  
**证明** 依定义. ∎

```agda
≼-antisym : Antisymmetric _≈_ _≼_
≼-antisym p q = p , q
```

**定理 2-3-13** $≈$ 是自反, 对称且传递的.  
**证明** 自反性和对称性依定义即得, 传递性依 $≼$ 的传递性即得. ∎

```agda
≈-refl : Reflexive _≈_
≈-refl = ≼-refl , ≼-refl

≈-sym : Symmetric _≈_
≈-sym (p , q) = q , p

≈-trans : Transitive _≈_
≈-trans (p , q) (u , v) = ≼-trans p u , ≼-trans v q
```

**事实 2-3-14** 内涵相等蕴含外延相等.

```agda
≡→≈ : a ≡ b → a ≈ b
≡→≈ refl = ≈-refl
```

**事实 2-3-15** 后继运算保持且单射 $≈$.  
**证明** 继承自 $≼$ 的性质. ∎

```agda
s≈s : suc preserves _≈_
s≈s (p , q) = s≼s p , s≼s q

s≈s-inj : suc injects _≈_
s≈s-inj (p , q) = s≼s-inj p , s≼s-inj q
```

**事实 2-3-16** 如果两条基本列逐项外延相等, 那么它们的极限外延相等.  
**证明** 继承自 $≼$ 的性质. ∎

```agda
l≈l : {wff : wf f} {wfg : wf g} → (∀ {n} → f n ≈ g n) → lim f ⦃ wff ⦄ ≈ lim g ⦃ wfg ⦄
l≈l p = l≼l (fst p) , l≼l (snd p)
```

**定理 2-3-17** 基本列去掉前 $n$ 项, 在外延的意义上不影响其极限.  
**证明** 我们只证去掉第一项的情况. 对任意基本列 $f$, 去掉第一项的基本列为 $f ∘ \text{suc}$, 要证 $\lim(f) ≈ \lim(f ∘ \text{suc})$.

- 先证 $\lim(f) ≼ \lim(f ∘ \text{suc})$, 只需证 $f(n)≼(f ∘ \text{suc})(n) = f(n^+)$, 由基本列的良构性即得.
- 再证 $\lim(f ∘ \text{suc}) ≼ \lim(f)$, 由 $(f ∘ \text{suc})(n) = f(n^+) ≼ \lim(f)$ 即得. ∎

```agda
l≈ls : {w : wf f} {ws : wf (f ∘ suc)} → lim f ⦃ w ⦄ ≈ lim (f ∘ ℕ.suc) ⦃ ws ⦄
l≈ls {w} = l≼l (≤→≼ (inl w)) , l≼ f≼l
```

## 严格序

**定义 2-3-18** 严格跨树关系 $a ≺ b := a^+ ≼ b$.

```agda
_≺_ : Rel; infix 6 _≺_
a ≺ b = suc a ≼ b
```

该定义是定理 2-1-17-(1) 和 定理 2-1-20 的跨树版本.

**事实 2-3-19** 零 ≺ 后继.  
**证明** $0 ≼ a → 0^+ ≼ a^+ = 0 ≺a^+$. ∎

```agda
z≺s : 0 ≺ suc a
z≺s = s≼s z≼
```

**事实 2-3-20** 事实 2-0-22 的跨树版本成立: $a ≼ b → a ≺ b^+$.  
**证明** 此即构造子 $\text{s≼s}$. ∎

```agda
≼→≺s : a ≼ b → a ≺ suc b
≼→≺s = s≼s
```

**事实 2-3-21** 定理 2-0-20 的跨树版本成立: $a ≺ b^+ → a ≼ b$.  
**证明** 此即事实 2-3-1. ∎

```agda
≺s→≼ : a ≺ suc b → a ≼ b
≺s→≼ p = s≼s-inj p
```

**定理 2-3-22** $≺$ 可以非严格化: $a ≺ b → a ≼ b$.  
**证明** 讨论 $p : a ≺ b = a^+ ≼ b$, 只可能有两种情况.

- 若 $p = \text{s≼s}(p') : a^+ ≼ b^+$, 必有 $p' : a ≼ b$, 所以 $p'^+ : a ≼ b^+$.
- 若 $p = \text{≼l}(p') : a^+ ≼ \lim(f)$, 必有 $p' : a^+ ≼ f(n)$. 由传递性即得 $a ≼ a^+ ≼ f(n) ≼ \lim(f)$. ∎

```agda
≺→≼ : a ≺ b → a ≼ b
≺→≼ (s≼s p) = ≼-suc p
≺→≼ (≼l p) = ≼l (≼-trans ≼-zero p)
```

**引理 2-3-23** 类似路径构造子, 我们有 $0 : a ≺ a^+$.  
**证明** $a ≼ a → a^+ ≼ a^+ = a ≺ a^+$. ∎

```agda
≺-zero : a ≺ suc a
≺-zero = s≼s ≼-refl
```

**引理 2-3-24** 类似路径构造子, 对任意 $p : a ≺ b$ 有 $p^+ : a ≺ b^+$.  
**证明** $a ≺ b → a ≼ b → a^+ ≼ b^+ = a ≺ b^+$. ∎

```agda
≺-suc : a ≺ b → a ≺ suc b
≺-suc p = s≼s (≺→≼ p)
```

**定理 2-3-25** 子树关系蕴含跨树关系: $a < b → a ≺ b$.  
**证明** 对路径 $r : a < b$ 归纳, 分三种情况.

- 若 $r = 0 : a < a^+$, 有 $0 : a ≺ a^+$.
- 若 $r = r'^+ : a < b^+$, 必有 $r' : a < b$, 由归纳假设有 $p : a ≺ b$, 所以 $p^+ : a ≺ b^+$.
- 若 $r = \lim(r') : a < \lim(f)$, 必有 $r' : a < f(n)$, 于是有 $a^+ ≤ f(n)$, 乃至 $a^+ ≼ f(n)$, 所以 $a^+ ≼ \lim(f)$, 即 $a < \lim(f)$. ∎

```agda
<→≺-rd : Road a b → a ≺ b
<→≺-rd zero = ≺-zero
<→≺-rd (suc r) = ≺-suc (<→≺-rd r)
<→≺-rd (lim r) = ≼l (≤→≼-rd (<→s≤-rd r))

<→≺ : a < b → a ≺ b
<→≺ r = <→≺-rd (set r)
```

**定理 2-3-26** $≺$ 满足传递性

- $a ≺ b → b ≺ c → a ≺ c$.
- $a ≺ b → b ≼ c → a ≺ c$.
- $a ≼ b → b ≺ c → a ≺ c$.

**证明** 继承自 $≼$ 的传递性. ∎

```agda
≺-trans : Transitive _≺_
≺-trans p q = ≼-trans p (≺→≼ q)

≺-≼-trans : Trans _≺_ _≼_ _≺_
≺-≼-trans p q = ≼-trans p q

≼-≺-trans : Trans _≼_ _≺_ _≺_
≼-≺-trans p q = ≼-trans (s≼s p) q
```

**推论 2-3-27** $≺$ 尊重 $≈$.  
**证明** 由定理 2-3-26 即得. ∎

```agda
≺-resp-≈ : _≺_ Respects₂ _≈_
≺-resp-≈ = (λ { (p , q) u → ≺-≼-trans u p })
         , (λ { (p , q) u → ≼-≺-trans q u })
```

**引理 2-3-28**

```agda
≺-acc : a ≼ b → Acc _≺_ b → Acc _≺_ a
≺-acc p (acc r) = acc (λ q → r (≺-≼-trans q p))
```

```agda
≺-wfnd : WellFounded _≺_
≺-wfnd zero    = acc λ ()
≺-wfnd (suc a) = acc λ { (s≼s p) → ≺-acc p (≺-wfnd a) }
≺-wfnd (lim f) = acc λ { (≼l p) → ≺-acc (≺→≼ p) (≺-wfnd (f _)) }
```

```agda
≺-irrefl : Irreflexive _≈_ _≺_
≺-irrefl = wf⇒irrefl ≺-resp-≈ ≈-sym ≺-wfnd

≺-asym : Asymmetric _≺_
≺-asym = wf⇒asym ≺-wfnd
```

## 结构实例化

由以上讨论可知 $≈$ 是等价关系, $≼$ 是相对于 $≈$ 的非严格偏序, $≺$ 是相对于 $≈$ 的严格偏序. 我们以此实例化标准库的抽象结构, 并得到第三套序关系推理链记法: `CrossTreeReasoning`.

```agda
open import Relation.Binary.Structures {A = Ord} _≈_

≈-isEquivalence : IsEquivalence
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans }

≼-isPreorder : IsPreorder _≼_
≼-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = fst
  ; trans = ≼-trans }

≼-isPartialOrder : IsPartialOrder _≼_
≼-isPartialOrder = record { isPreorder = ≼-isPreorder ; antisym = ≼-antisym }

≺-isStrictPartialOrder : IsStrictPartialOrder _≺_
≺-isStrictPartialOrder = record
  { isEquivalence = ≈-isEquivalence
  ; irrefl = ≺-irrefl
  ; trans = ≺-trans
  ; <-resp-≈ = ≺-resp-≈ }

module CrossTreeReasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    {_≈_ = _≈_} {_≤_ = _≼_} {_<_ = _≺_}
    ≼-isPreorder ≺-asym ≺-trans ≺-resp-≈ ≺→≼ ≺-≼-trans ≼-≺-trans
    public
```

## 跨树算术定理

### 加法

```agda
+a-infl≼ : (_+ a) inflates _≼_
+a-infl≼ = ≤→≼ +-infl≤

+a-infl≺ : ⦃ NonZero a ⦄ → (_+ a) inflates _≺_
+a-infl≺ = <→≺ +-infl
```

```agda
a+-infl≼ : (a +_) inflates _≼_
a+-infl≼ {x = zero}  = z≼
a+-infl≼ {x = suc x} = s≼s a+-infl≼
a+-infl≼ {x = lim f} = l≼l a+-infl≼
```

```agda
1+l-absorb : isLim a → 1 + a ≈ a
1+l-absorb {lim f} tt = l≼ls (aux (<→≺ it)) , l≼l a+-infl≼ where
  aux : a ≺ b → 1 + a ≼ b
  aux {(zero)} (s≼s p) = z≺s
  aux {suc a} (s≼s p)  = s≼s (aux p)
  aux {lim f} (s≼s p)  = l≼ (aux (s≼s (≼-trans f≼l p)))
  aux (≼l p) = ≼l (aux p)
```

```agda
a+-pres≼ : (a +_) preserves _≼_
a+-pres≼ z≼       = +a-infl≼
a+-pres≼ (s≼s p)  = s≼s (a+-pres≼ p)
a+-pres≼ (≼l p)   = ≼l (a+-pres≼ p)
a+-pres≼ (l≼ p)   = l≼ (a+-pres≼ p)
```

```agda
a+-pres≺ : (a +_) preserves _≺_
a+-pres≺ (s≼s p) = s≼s (a+-pres≼ p)
a+-pres≺ (≼l p)  = ≼l (a+-pres≼ p)
```

```agda
+a-pres≼ : (_+ a) preserves _≼_
+a-pres≼ {(zero)} p = p
+a-pres≼ {suc a} p  = s≼s (+a-pres≼ p)
+a-pres≼ {lim f} p  = l≼l (+a-pres≼ p)
```

```agda
+-pres≼ : a ≼ b → c ≼ d → a + c ≼ b + d
+-pres≼ {a} {b} {c} {d} p q = begin
  a + c                     ≤⟨ a+-pres≼ q ⟩
  a + d                     ≤⟨ +a-pres≼ p ⟩
  b + d                     ∎ where open CrossTreeReasoning
```

```agda
a+-cong≈ : b ≈ c → a + b ≈ a + c
a+-cong≈ (p , q) = a+-pres≼ p , a+-pres≼ q

+a-cong≈ : b ≈ c → b + a ≈ c + a
+a-cong≈ (p , q) = +a-pres≼ p , +a-pres≼ q
```

### 乘法

```agda
a*-pres≼ : ⦃ _ : NonZero a ⦄ → (a *_) preserves _≼_
a*-pres≼ z≼       = z≼
a*-pres≼ (s≼s p)  = +a-pres≼ (a*-pres≼ p)
a*-pres≼ (≼l p)   = ≼l (a*-pres≼ p)
a*-pres≼ (l≼ p)   = l≼ (a*-pres≼ p)
```

```agda
*a-infl≼ : ⦃ NonZero a ⦄ → (_* a) inflates _≼_ within NonZero
*a-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ a*-id ⟩
  x * 1                     ≤⟨ a*-pres≼ (<→≺ nz-elim) ⟩
  x * a                     ∎ where open CrossTreeReasoning
```

```agda
a*-pres≺ : ⦃ _ : NonZero a ⦄ → (a *_) preserves _≺_
a*-pres≺ {a} {x} (s≼s {b} p) = begin-strict
  a * x                     <⟨ +a-infl≺ ⟩
  a * x + a                 ≤⟨ +a-pres≼ (a*-pres≼ p) ⟩
  a * b + a                 ∎ where open CrossTreeReasoning
a*-pres≺ {a} {x} (≼l {f} {n} p) = begin-strict
  a * x                     <⟨ a*-pres≺ p ⟩
  a * f n                   ≤⟨ f≼l ⟩
  lim- (λ n → a * f n)      ∎ where open CrossTreeReasoning
```

```agda
*a-infl≺ : ⦃ NonTrivial a ⦄ → (_* a) inflates _≺_ within NonZero
*a-infl≺ {a} {x} =          begin-strict
  x                         ≈˘⟨ ≡→≈ a*-id ⟩
  x * 1                     <⟨ a*-pres≺ (<→≺ nt-elim) ⟩
  x * a                     ∎ where open CrossTreeReasoning
```

```agda
*a-pres≼ : (_* a) preserves _≼_ within NonZero
*a-pres≼ {(zero)} _ = ≼-refl
*a-pres≼ {lim f} p = l≼l (*a-pres≼ p)
*a-pres≼ {suc a} {x} {y} p = begin
  x * a + x                 ≤⟨ a+-pres≼ p ⟩
  x * a + y                 ≤⟨ +a-pres≼ (*a-pres≼ p) ⟩
  y * a + y                 ∎ where open CrossTreeReasoning
```

```agda
a*-infl≼ : ⦃ _ : NonZero a ⦄ → (a *_) inflates _≼_
a*-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ *a-id ⟩
  (1 * x) ⦃ _ ⦄             ≤⟨ *a-pres≼ ⦃ _ ⦄ (<→≺ nz-elim) ⟩
  a * x                     ∎ where open CrossTreeReasoning
```

```agda
a*-cong≈ : ⦃ _ : NonZero a ⦄ → b ≈ c → a * b ≈ a * c
a*-cong≈ (p , q) = a*-pres≼ p , a*-pres≼ q

*a-cong≈ : ⦃ _ : NonZero b ⦄ ⦃ _ : NonZero c ⦄ → b ≈ c → b * a ≈ c * a
*a-cong≈ (p , q) = *a-pres≼ p , *a-pres≼ q
```

## 幂运算

```agda
a^-pres≼ : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _≼_
a^-pres≼ z≼ = <→≺ nz-elim                 where instance _ = ^-nz
a^-pres≼ (s≼s p) = *a-pres≼ (a^-pres≼ p)  where instance _ = ^-nz
a^-pres≼ (≼l p) = ≼l (a^-pres≼ p)
a^-pres≼ (l≼ p) = l≼ (a^-pres≼ p)
```

```agda
^a-infl≼ : ⦃ NonZero a ⦄ → (_^ a) inflates _≼_ within NonTrivial
^a-infl≼ {a} {x} =          begin
  x                         ≈˘⟨ ≡→≈ a^-id ⟩
  x ^ 1                     ≤⟨ a^-pres≼ (<→≺ nz-elim) ⟩
  x ^ a                     ∎ where open CrossTreeReasoning
```

```agda
a^-pres≺ : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _≺_
a^-pres≺ {a} {x} (s≼s {b} p) = begin-strict
  a ^ x                     <⟨ *a-infl≺ ⟩
  a ^ x * a                 ≤⟨ *a-pres≼ (a^-pres≼ p) ⟩
  a ^ b * a                 ∎ where open CrossTreeReasoning; instance _ = ^-nz
a^-pres≺ {a} {x} (≼l {f} {n} p) = begin-strict
  a ^ x                     <⟨ a^-pres≺ p ⟩
  a ^ f n                   ≤⟨ f≼l ⟩
  lim- (λ n → a ^ f n)      ∎ where open CrossTreeReasoning
```

```agda
^a-infl≺ : ⦃ NonTrivial a ⦄ → (_^ a) inflates _≺_ within NonTrivial
^a-infl≺ {a} {x} =          begin-strict
  x                         ≈˘⟨ ≡→≈ a^-id ⟩
  x ^ 1                     <⟨ a^-pres≺ (<→≺ nt-elim) ⟩
  x ^ a                     ∎ where open CrossTreeReasoning
```

```agda
^a-pres≼ : (_^ a) preserves _≼_ within NonTrivial
^a-pres≼ {(zero)} _ = ≼-refl
^a-pres≼ {lim f} p = l≼l (^a-pres≼ p)
^a-pres≼ {suc a} {x} {y} p = begin
  x ^ a * x                 ≤⟨ a*-pres≼ p ⟩
  x ^ a * y                 ≤⟨ *a-pres≼ (^a-pres≼ p) ⟩
  y ^ a * y                 ∎ where open CrossTreeReasoning; instance _ = ^-nz
```

```agda
a^-infl≼ : ⦃ _ : NonTrivial a ⦄ → (a ^_) inflates _≼_
a^-infl≼ {a} {x} =          begin
  x                         ≤⟨ aux ⟩
  (2 ^ x) ⦃ _ ⦄             ≤⟨ ^a-pres≼ ⦃ _ ⦄ (<→≺ nt-elim) ⟩
  a ^ x                     ∎ where
  open CrossTreeReasoning
  instance _ : NonTrivial 2   ; _ = _
  instance _ : NonZero (2 ^ b); _ = ^-nz
  aux : b ≼ 2 ^ b
  aux {(zero)} = z≼
  aux {lim f} = l≼l aux
  aux {suc b} =             begin
    b + 1                   ≤⟨ +a-pres≼ aux ⟩
    2^b + 1                 ≤⟨ a+-pres≼ (<→≺ nz-elim) ⟩
    2^b + 2^b               ≈˘⟨ ≡→≈ (cong (_+ 2^b) +a-id) ⟩
    0 + 2^b + 2^b           ∎ where 2^b = 2 ^ b
```

```agda
a^-cong≈ : ⦃ _ : NonTrivial a ⦄ → b ≈ c → a ^ b ≈ a ^ c
a^-cong≈ (p , q) = a^-pres≼ p , a^-pres≼ q

^a-cong≈ : ⦃ _ : NonTrivial b ⦄ ⦃ _ : NonTrivial c ⦄ → b ≈ c → b ^ a ≈ c ^ a
^a-cong≈ (p , q) = ^a-pres≼ p , ^a-pres≼ q
```

```agda
+-assoc-n : ⦃ _ : NonZero a ⦄ → a + a * fin n ≡ a * fin n + a
+-assoc-n {n = zero} = sym +a-id
+-assoc-n {a} {n = suc n} = begin-equality
  a + a * suc (fin n)     ≈⟨ refl ⟩
  a + (a * fin n + a)     ≈⟨ +-assoc ⟩
  a + a * fin n + a       ≈⟨ cong (_+ a) +-assoc-n ⟩
  a * suc (fin n) + a     ∎ where open SubTreeReasoning
```

```agda
ω^-absorb : a ≺ b → ω ^ a + ω ^ b ≈ ω ^ b
ω^-absorb {a} {b = suc b} (s≼s a≼b) =
  (l≼ λ {n} →               begin
    ω ^ a + ω ^ b * fin n   ≤⟨ +a-pres≼ (a^-pres≼ a≼b) ⟩
    ω ^ b + ω ^ b * fin n   ≈⟨ ≡→≈ +-assoc-n ⟩
    ω ^ b * fin n + ω ^ b   ≈⟨ ≈-refl ⟩
    ω ^ b * suc (fin n)     ≤⟨ a*-pres≼ (<→≺ n<ω) ⟩
    ω ^ b * ω               ∎) ,
  (l≼ λ {n} →               begin
    ω ^ b * fin n           ≤⟨ a+-infl≼ ⟩
    ω ^ a + ω ^ b * fin n   ≤⟨ a+-pres≼ (a*-pres≼ $ ≤→≼ $ inl n<ω) ⟩
    ω ^ a + ω ^ b * ω       ∎) where
  open CrossTreeReasoning
  instance _ = ^-nz
ω^-absorb {a} {b = lim f} (≼l {n} a≺fn) = l≼ aux , l≼l a+-infl≼ where
  open CrossTreeReasoning
  aux : ω ^ a + ω ^ f m ≼ lim- (λ m → ω ^ f m)
  aux {m} with <-cmp n m
  ... | tri< n<m _ _ = ≼l $ begin
    ω ^ a + ω ^ f m         ≤⟨ fst (ω^-absorb a≺fm) ⟩
    ω ^ f m                 ∎ where
    a≺fm =                  begin-strict
      a                     <⟨ a≺fn ⟩
      f n                   <⟨ <→≺ (seq-pres n<m) ⟩
      f m                   ∎
  ... | tri≈ _ refl _ = ≼l $ begin
    ω ^ a + ω ^ f n         ≤⟨ fst (ω^-absorb a≺fn) ⟩
    ω ^ f n                 ∎
  ... | tri> _ _ m<n = ≼l $ begin
    ω ^ a + ω ^ f m         ≤⟨ a+-pres≼ (a^-pres≼ fm≼fn) ⟩
    ω ^ a + ω ^ f n         ≤⟨ fst (ω^-absorb a≺fn) ⟩
    ω ^ f n                 ∎ where
    fm≼fn =                 begin
      f m                   <⟨ <→≺ (seq-pres m<n) ⟩
      f n                   ∎
```
