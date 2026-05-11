# 形式化大数数学 (3.0 - 布劳威尔树壁垒序数)

> 交流Q群: 893531731  
> 本文源码: [BTBO.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/OCF/BTBO.lagda.md)  
> 高亮渲染: [BTBO.html](https://choukh.github.io/agda-googology/OCF.BTBO.html)  
> 纯代码版: [BTBO.agda](https://gist.github.com/choukh/d7ca58dd90ee112162debce78eb7ad78)

我们主张的形式化大数基于以下纲领:

1. 序数先行
   - 先实现序数再折叠成大数
   - 排除很难分析序数上下界的函数以及非序数增长率函数
2. 理想计算机可运行
   - 在以类型论为基础的证明助理中无公理地写出定义
3. 保证停机
   - 通过证明助理的自动停机检查器保证停机

本文可能是《形式化大数》系列的最后一篇, 因为遵循该纲领, 我们目前卡在了 $\psi(\Omega_\Omega)$. 为了引起关注, 我们将其命名为布劳威尔树壁垒序数 (Brouwer Tree Barrier Ordinal), 简称 BTBO. 本文将介绍该序数的实现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.BTBO where
open import Function using (_∘_; it)
```

## 布劳威尔树

什么是布劳威尔树? 从零开始 (字面意义), 我们能看得更清晰一些.

**定义 (布劳威尔树)**  

$$
\begin{align}
\mathbf{0}&:=
\\[2em]
\mathbf{1}&:=\cfrac{\;\mathbf{0}\to\mathbf{1}\;}{\mathbf{1}}\;\mathsf{zero}
\\[2em]
\mathbb{N}&:=\cfrac{\;\mathbf{0}\to\mathbb{N}\;}{\mathbb{N}}\;\mathsf{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{N}\;}{\mathbb{N}}\;\mathsf{suc}
\\[2em]
\mathbb{O}_0&:=\cfrac{\;\mathbf{0}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\mathsf{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\mathsf{suc}\;\;\;\;\cfrac{\;\mathbb{N}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\mathsf{lim}
\\[2em]
\mathbb{O}_1&:=\cfrac{\;\mathbf{0}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\mathsf{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\mathsf{suc}\;\;\;\;\cfrac{\;\mathbb{N}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\mathsf{lim}\;\;\;\;\cfrac{\;\mathbb{O}_0\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\mathsf{lim}_1
\end{align}
$$

```agda
module Brw-Basic where

  data 𝟎 : Set where

  data 𝟏 : Set where
    zero  : (𝟎 → 𝟏) → 𝟏

  data ℕ : Set where
    zero  : (𝟎 → ℕ) → ℕ
    suc   : (𝟏 → ℕ) → ℕ

  data O₀ : Set where
    zero  : (𝟎 → O₀) → O₀
    suc   : (𝟏 → O₀) → O₀
    lim   : (ℕ → O₀) → O₀

  data O₁ : Set where
    zero  : (𝟎 → O₁) → O₁
    suc   : (𝟏 → O₁) → O₁
    lim   : (ℕ → O₁) → O₁
    lim₁  : (O₀ → O₁) → O₁
```

这样的一系列类型就叫**布劳威尔树**, 它们的项所能表示的序数就叫布劳威尔树序数. 不难看出

- `𝟎` 与标准库的 `⊥` 同构
- `𝟏` 与标准库的 `⊤` 同构
- `ℕ` 与标准库的 `ℕ` 同构

```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)
```

而 `O₀` 和 `O₁` 又与如下定义的 `Ord₀`, `Ord₁` 同构

```agda
module Ord-Basic where
  data Ord₀ : Set where
    zero : Ord₀
    suc : Ord₀ → Ord₀
    lim : (ℕ → Ord₀) → Ord₀

  data Ord₁ : Set where
    zero : Ord₁
    suc : Ord₁ → Ord₁
    lim₀ : (ℕ → Ord₁) → Ord₁
    lim₁ : (Ord₀ → Ord₁) → Ord₁
```

`O₀`, `O₁` 的定义方便往上归纳定义 $\mathsf{Brw}_\alpha$, 而 `Ord₀`, `Ord₁` 则方便直接使用.

为了方便表述, 我们把这些类型记作 $\mathsf{Brw}_\alpha$ 或者 $\mathsf{Ord}_\alpha$. 它们有如下关系

$$
\mathsf{Ord}_\alpha :=
\begin{cases}
   \mathsf{Brw}_{\alpha+3} &\text{if } \alpha < \omega \\
   \mathsf{Brw}_\alpha &\text{if } \alpha\ge\omega
\end{cases}
$$

当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

将布劳威尔树 $\mathsf{Brw}_\alpha$ 所能表示的序数的上确界记作 $\sup(\mathsf{Brw}_\alpha)$, 并按 Buchholz 的惯例令

$$
\Omega_\alpha :=
\begin{cases}
   1 &\text{if } \alpha = 0 \\
   \omega_\alpha &\text{if } \alpha > 0
\end{cases}
$$

其中 $\Omega_1$ 简记作 $\Omega$, 则有

$$
\begin{align}
\sup(\mathsf{Brw}_0) &= 0 \\
\sup(\mathsf{Brw}_1) &= 1 \\
\sup(\mathsf{Brw}_2) &= \omega \\
\sup(\mathsf{Brw}_3) &= \Omega \\
\sup(\mathsf{Brw}_4) &= \Omega_2 \\
...
\end{align}
$$

**约定** 如果一个类型 `A` 被当作序数, 我们指该类型所能表示的序数的上确界 $\sup(A)$.

考虑 $\mathsf{Brw}_{\alpha^+}$ 到 $\mathsf{Brw}_{\alpha}$ 的折叠. 从最底层开始, $\mathsf{Brw}_1$ 到 $\mathsf{Brw}_0$ 以及 $\mathsf{Brw}_2$ 到 $\mathsf{Brw}_1$ 的折叠是平凡的. 而 $\mathsf{Brw}_3$ 到 $\mathsf{Brw}_2$ 的折叠就是各种增长层级. 再往后的折叠就是通常所说的 OCF.

只不过通常的 OCF 使用集合论语言的非直谓定义, 而我们这里需要具体的递归算法一层一层往下: 从 $\mathsf{Brw}_\alpha$ 到 ... 到 $\mathsf{Brw}_4$ 到 $\mathsf{Brw}_3$ (大可数序数), 最后到 $\mathsf{Brw}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\mathsf{Brw}_\alpha$, 二是一层层折叠到 $\mathsf{Brw}_2$. 只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一附加很多要求. 我们一步步来.

## 自然数层布劳威尔树

我们需要等号 `_≡_` 及其性质.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

transport : {A B : Set} → A ≡ B → A → B
transport refl x = x
```

**定义** 自然数上的 $<$ 序  

$$
\cfrac{}{\;n<n^+\;}\;\;\mathsf{zero}\;\;\;\;\;\;\;\cfrac{n<m}{\;n<m^+\;}\;\;\mathsf{suc}
$$

```agda
module Nat-Lt where
  variable n m o : ℕ

  data _<_ : ℕ → ℕ → Set where
    zero : n < suc n
    suc  : n < m → n < suc m
```

**约定** 为了简化表述, 我们采用以下记法约定:

- 项 $\mathsf{zero}$ 可简记为 $0$.
- 项 $\mathsf{suc}(x)$ 可简记为 $x^+$.
- 当它们为布劳威尔树项之间关系的证明时, 同样采用此约定.

因此我们可以写 $0_x:x<x^+$, 以及 $p^+:x<y^+$ (此时有 $p:x<y$).

由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\mathsf{Brw}_n$. 伪代码如下

```pseudocode
data Brw₀ : Set where
data Brwₖ₊₁ : Set where
  cf₀ : (Brw₀ → Brwₖ₊₁) → Brwₖ₊₁
  cf₁ : (Brw₁ → Brwₖ₊₁) → Brwₖ₊₁
  ...
  cfₖ : (Brwₖ → Brwₖ₊₁) → Brwₖ₊₁
```

其中 `Brwₖ₊₁` 的下标 `k + 1` 代表了该类型的构造子的个数, 而下标为 `k` 的构造子 `cfₖ` 则构造了共尾度 (基本列的长度) 为 `Brwₖ` 的序数.

- `cf₀` 构造了共尾度为 $0$ 的序数, 它只有一个, 就是空列 `λ ()`, 代表序数 $0$
- `cf₁` 构造了共尾度为 $1$ 的序数, 即后继序数.
- `cf₂` 构造了共尾度为 $\omega$ 的序数, 可表示可数极限序数.
- `cf₃` 构造了共尾度为 $\Omega$ 的序数, 可表示不可数极限序数.
- `cf₄` 构造了共尾度为 $\Omega_2$ 的序数, 可表示更高阶的不可数极限序数.
- ...

归纳这个模式, 我们可以定义 `Brw : ℕ → Set` 这个类型族. 核心思想是通过类似类型论塔斯基宇宙的形式来定义自然数索引的布劳威尔树族。对于给定的层数 $n$, 我们首先假设所有更低层的树 $\mathsf{Brw}_{<i}$（其中 $i < n$）都已经定义好, 然后定义第 $n$ 层的树 $\mathsf{Brw}_n$。具体地, $\mathsf{Brw}_n$ 的每个元素都可以通过构造子 $\mathsf{cf}$ 来构造, 该构造子接受一个证明 $p : i < n$ 和一个函数 $f : \mathsf{Brw}_{<i} \to \mathsf{Brw}_n$, 表示该元素的共尾度为 $\mathsf{Brw}_{<i}$。函数 `Brw<` 处理了层次之间的依赖关系, 而 `Brw` 则是对外的接口, 将第 $n$ 层的树定义为 $\mathsf{Brw}_{<n, 0_n}$。

**定义 (自然数层布劳威尔树)**  

$$
\begin{align}
\mathsf{Brw}_+(n, \mathsf{Brw}_{<}) &:= \cfrac{\;(p:i<n)\;\;\;(f:\mathsf{Brw}_{<}(i,p)\to\mathsf{Brw}_+)\;}{\mathsf{Brw}_+}\;\mathsf{cf}
\\[1.5em]
\mathsf{Brw}_{<}(i, p) &:= 
\begin{cases}
   \mathsf{Brw}_+(i, \mathsf{Brw}_{<}) &\text{if } p = (0_i:i<i^+) \\
   \mathsf{Brw}_{<}(i, q) &\text{if } p = (q^+:i<m^+)
\end{cases}
\\[1.5em]
\mathsf{Brw}_n &:= \mathsf{Brw}_{<}(n,0_n)
\end{align}
$$

```agda
module Brw-Nat where
  open Nat-Lt
  private variable i : ℕ

  -- 假设下标为 `i < n` 的任意树 `Brw< i` 已经定义完成, 定义下标为 `n` 的树 `Brw₊`
  module _ (n : ℕ) (Brw< : ∀ i → i < n → Set) where
    data Brw₊ : Set where
      -- `Brw₊` 的元素的共尾度为任意满足 `i < n` 的 `Brw< i`
      cf : (p : i < n) (f : Brw< i p → Brw₊) → Brw₊

  -- 给定 `n`, 递归定义满足 `p : i < n` 的任意 `i` 所给出的树 `Brw< i p`
  Brw< : ∀ i → i < n → Set
  Brw< i zero = Brw₊ i Brw<
  Brw< i (suc p) = Brw< i p

  -- 消掉 `i < n` 条件
  Brw : ℕ → Set
  Brw n = Brw< n zero
```

这样我们就定义了任意 $\mathsf{Brw}_n$. 虽然它只需要一个构造子“族”, 非常优雅, 但不方便使用. 从现在起我们改用 $\mathsf{Ord}_n$ 层级, 显式写出最初的三个构造子 `zero`, `suc`, `lim`, 其后才使用 `limᵢ` 族.

**定义 (显式构造子的布劳威尔树族)**  

$$
\begin{align}
\mathsf{Ord}_+(n, \mathsf{Ord}_{<}) &:= 
\cfrac{}{\mathsf{Ord}_+}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_+\;}{\mathsf{Ord}_+}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_+\;}{\mathsf{Ord}_+}\;\mathsf{lim}
\\[2em]
&\;\;\;\;\cfrac{\;(p:i<n)\;\;\;(\mathsf{Ord}_{<}(i,p)\to\mathsf{Ord}_+)\;}{\mathsf{Ord}_+}\;\mathsf{lim}_i
\end{align}
$$

```agda
module Ord-Nat where
  open Nat-Lt public
  private variable i : ℕ

  module _ (n : ℕ) (Ord< : ∀ i → i < n → Set) where
    data Ord₊ : Set where
      zero : Ord₊
      suc  : Ord₊ → Ord₊
      lim  : (f : ℕ → Ord₊) → Ord₊
      limᵢ : (p : i < n) (f : Ord< i p → Ord₊) → Ord₊
```

剩下的定义跟 $\mathsf{Brw}_n$ 是一样的. 给定 $n$, 我们递归定义满足 $p:i<n$ 的任意 $i$ 所给出的树

$$
\mathsf{Ord}_{<}(i, p) := 
\begin{cases}
   \mathsf{Ord}_+(i, \mathsf{Ord}_{<}) &\text{if } p = (0_i:i<i^+) \\
   \mathsf{Ord}_{<}(i, q) &\text{if } p = (q^+:i<m^+)
\end{cases}
$$

并定义

$$
\mathsf{Ord}_n := \mathsf{Ord}_{<}(n,0_n)
$$

```agda
  Ord< : ∀ i → i < n → Set
  Ord< i zero = Ord₊ i Ord<
  Ord< i (suc p) = Ord< i p

  Ord : ℕ → Set
  Ord n = Ord< n zero
```

**定理** $\mathsf{Ord}_{<}(i,\;p:i<n)$ 与 $\mathsf{Ord}_{<}(i,\;q:i<m)$ 表示相同的树.  
**证明** 对证明 $p:i<n$ 和 $q:i<m$ 归纳. 由 $\mathsf{Ord}_{<}$ 的定义:

- 若 $p=(0_i:i<i^+),\;q=(0_i:i<i^+)$, 则 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_+(i, \mathsf{Ord}_{<}) = \mathsf{Ord}_{<}(i,q)$.
- 若 $p=(p'^+:i<n^+),\;q=(0_i:i<i^+)$, 则 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,p')$, 由归纳假设 $\mathsf{Ord}_{<}(i,p') = \mathsf{Ord}_{<}(i,q)$.
- 若 $p:i<n,\;q=q'^+:i<m^+$, 则 $\mathsf{Ord}_{<}(i,q) = \mathsf{Ord}_{<}(i,q')$, 由归纳假设直接得 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,q')$. ∎

```agda
  Ord<-≡ : (p : i < n) (q : i < m) → Ord< i p ≡ Ord< i q
  Ord<-≡ zero zero      = refl
  Ord<-≡ (suc p) zero   = Ord<-≡ p zero
  Ord<-≡ p (suc q)      = Ord<-≡ p q
```

也就是说 $\mathsf{Ord}_{<}(i,\;p:i<n)$ 与 $p$ 和 $n$ 无关, 我们改记作 $\mathsf{Ord}_{<i<\_}$.

```agda
  coe : {p : i < n} {q : i < m} → Ord< i p → Ord< i q
  coe {p} {q} = transport (Ord<-≡ p q)

  coe₀ : {p : i < m} → Ord i → Ord< i p
  coe₀ = coe {p = zero}
```

## $\omega \cdot 2$ 层布劳威尔树

继续往上, 把 `Ord : ℕ → Set` 封装进构造子 $\mathsf{lim}_n$, 它允许构造共尾度为任意 $\sup(\mathsf{Ord}_n)$ 的序数, 这样就得到了 $\mathsf{Ord}_\omega$.

**定义 ($\omega$层树)**  

$$
\mathsf{Ord}_\omega := 
\cfrac{}{\mathsf{Ord}_\omega}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_\omega\;}{\mathsf{Ord}_\omega}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_\omega\;}{\mathsf{Ord}_\omega}\;\mathsf{lim}
\;\;\;\;
\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_n\to\mathsf{Ord}_\omega)\;}{\mathsf{Ord}_\omega}\;\mathsf{lim}_n
$$

```agda
  data Ordω : Set where
    zero : Ordω
    suc  : Ordω → Ordω
    lim  : (f : ℕ → Ordω) → Ordω
    limₙ : (n : ℕ) (f : Ord n → Ordω) → Ordω
```

再添加共尾度为 $\sup(\mathsf{Ord}_\omega)$ 的序数, 就得到了 $\mathsf{Ord}_{\omega+1}$.

**定义 ($\omega+1$ 层树)**  

$$
\begin{align}
\mathsf{Ord}_{\omega+1} &:= 
\cfrac{}{\mathsf{Ord}_{\omega+1}}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_{\omega+1}\;}{\mathsf{Ord}_{\omega+1}}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_{\omega+1}\;}{\mathsf{Ord}_{\omega+1}}\;\mathsf{lim}
\\[1em]
&\;\;\;\;\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_n\to\mathsf{Ord}_{\omega+1})\;}{\mathsf{Ord}_{\omega+1}}\;\mathsf{lim}_n
\;\;\;\;
\cfrac{\;\mathsf{Ord}_\omega\to\mathsf{Ord}_{\omega+1}\;}{\mathsf{Ord}_{\omega+1}}\;\mathsf{lim}_\omega
\end{align}
$$

```agda
  data Ordω+1 : Set where
    zero : Ordω+1
    suc  : Ordω+1 → Ordω+1
    lim  : (f : ℕ → Ordω+1) → Ordω+1
    limₙ : (n : ℕ) (f : Ord n → Ordω+1) → Ordω+1
    limω : (f : Ordω → Ordω+1) → Ordω+1
```

重复上述过程可以得到 $\mathsf{Ord}_{\omega+n}$, $\mathsf{Ord}_{\omega \cdot 2}$ 和 $\mathsf{Ord}_{\omega \cdot 2+1}$.

**定义 ($\omega \cdot 2$ 层树)**  

$$
\begin{align}
\mathsf{Ord}_{\omega+}(n, \mathsf{Ord}_{\omega<}) &:= 
\cfrac{}{\mathsf{Ord}_{\omega+}}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_{\omega+}\;}{\mathsf{Ord}_{\omega+}}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_{\omega+}\;}{\mathsf{Ord}_{\omega+}}\;\mathsf{lim}
\\[1em]
&\;\;\;\;\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_n\to\mathsf{Ord}_{\omega+})\;}{\mathsf{Ord}_{\omega+}}\;\mathsf{lim}_n
\;\;\;\;
\cfrac{\;(k:\mathbb{N})\;(p:k<n)\;\;\;(\mathsf{Ord}_{\omega<}(k,p)\to\mathsf{Ord}_{\omega+})\;}{\mathsf{Ord}_{\omega+}}\;\mathsf{lim}_{\omega+k}
\\[2em]
\mathsf{Ord}_{\omega<}(k, p) &:= 
\begin{cases}
   \mathsf{Ord}_{\omega+}(k, \mathsf{Ord}_{\omega<}) &\text{if } p = (0_k:k<k^+) \\
   \mathsf{Ord}_{\omega<}(k, q) &\text{if } p = (q^+:k<m^+)
\end{cases}
\\[1em]
\mathsf{Ord}_{\omega+n} &:= \mathsf{Ord}_{\omega<}(n,0_n)
\\[2em]
\mathsf{Ord}_{\omega \cdot 2} &:= 
\cfrac{}{\mathsf{Ord}_{\omega \cdot 2}}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_{\omega \cdot 2}\;}{\mathsf{Ord}_{\omega \cdot 2}}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_{\omega \cdot 2}\;}{\mathsf{Ord}_{\omega \cdot 2}}\;\mathsf{lim}
\\[1em]
&\;\;\;\;\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_n\to\mathsf{Ord}_{\omega \cdot 2})\;}{\mathsf{Ord}_{\omega \cdot 2}}\;\mathsf{lim}_n
\;\;\;\;
\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_{\omega+n}\to\mathsf{Ord}_{\omega \cdot 2})\;}{\mathsf{Ord}_{\omega \cdot 2}}\;\mathsf{lim}_{\omega+n}
\\[2em]
\mathsf{Ord}_{\omega \cdot 2+1} &:= 
\cfrac{}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_{\omega \cdot 2+1}\;}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_{\omega \cdot 2+1}\;}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{lim}
\\[1em]
&\;\;\;\;\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_n\to\mathsf{Ord}_{\omega \cdot 2+1})\;}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{lim}_n
\;\;\;\;
\cfrac{\;(n:\mathbb{N})\;\;\;(\mathsf{Ord}_{\omega+n}\to\mathsf{Ord}_{\omega \cdot 2+1})\;}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{lim}_{\omega+n}
\\[1em]
&\;\;\;\;\cfrac{\;\mathsf{Ord}_{\omega \cdot 2}\to\mathsf{Ord}_{\omega \cdot 2+1}\;}{\mathsf{Ord}_{\omega \cdot 2+1}}\;\mathsf{lim}_{\omega \cdot 2}
\end{align}
$$

```agda
  module _ (n : ℕ) (Ordω< : ∀ k → k < n → Set) where
    data Ordω₊ : Set where
      zero  : Ordω₊
      suc   : Ordω₊ → Ordω₊
      lim   : (f : ℕ → Ordω₊) → Ordω₊
      limₙ  : (n : ℕ) (f : Ord n → Ordω₊) → Ordω₊
      limω+ : (k : ℕ) (p : k < n) (f : Ordω< k p → Ordω₊) → Ordω₊

  Ordω< : ∀ {n} k → k < n → Set
  Ordω< k zero = Ordω₊ k Ordω<
  Ordω< k (suc p) = Ordω< k p

  Ordω+ : ℕ → Set
  Ordω+ n = Ordω< n zero

  data Ordω2 : Set where
    zero  : Ordω2
    suc   : Ordω2 → Ordω2
    lim   : (f : ℕ → Ordω2) → Ordω2
    limₙ  : (n : ℕ) (f : Ord n → Ordω2) → Ordω2
    limω+ : (n : ℕ) (f : Ordω+ n → Ordω2) → Ordω2

  data Ordω2+1 : Set where
    zero  : Ordω2+1
    suc   : Ordω2+1 → Ordω2+1
    lim   : (f : ℕ → Ordω2+1) → Ordω2+1
    limₙ  : (n : ℕ) (f : Ord n → Ordω2+1) → Ordω2+1
    limω+ : (n : ℕ) (f : Ordω+ n → Ordω2+1) → Ordω2+1
    limω2 : (f : Ordω2 → Ordω2+1) → Ordω2+1
```

## 内 $\Omega$ 数

前面说过, 一个布劳威尔树类型 `Ord n` 本身可以视作一个 $\Omega$ 数, 代表该类型的项所能表示的序数的上确界. 现在我们转而研究该类型的项所能表示的 $\Omega$ 数, 我们称为**内 $\Omega$ 数**. 其中最大的那个, 称为最大内 $\Omega$ 数.

**定义 (层级提升函数)** 对任意 $n : \mathbb{N}$, 递归定义 $\text{Ord}_n$ 到 $\text{Ord}_{n^+}$ 的嵌入 $↑_+$ 如下:

- 如果 $a : \text{Ord}_n$ 由 $\mathsf{zero}$, $\mathsf{suc}$ 或 $\mathsf{lim}$ 构造, 我们直接使用 $\text{Ord}_{n^+}$ 的同名构造子递归构造 $↑_+a$.
- 如果 $a = \mathsf{lim}_n(p,f)$, 其中 $p:i<n$ 且 $f:\mathsf{Ord}_{<}(i,\;p)\to\text{Ord}_n$, 则 $↑_+a:=\mathsf{lim}_n(p^+,↑_+\circ f)$, 其中 $p^+:i<n^+$ 且 $(↑_+\circ f):\mathsf{Ord}_{<}(i,\;p)\to\text{Ord}_{n^+}$.

```agda
  ↑₊ : Ord n → Ord (suc n)
  ↑₊ zero = zero
  ↑₊ (suc a) = suc (↑₊ a)
  ↑₊ (lim f) = lim (↑₊ ∘ f)
  ↑₊ (limᵢ p f) = limᵢ (suc p) (↑₊ ∘ f)
```

向上嵌入允许我们在 $\text{Ord}_{n^+}$ 中表达 $↑_+:\text{Ord}_{n}\to\text{Ord}_{n^+}$ 的极限, 该极限就是我们所需的最大内 $\Omega$ 数.

**定义 (Ω数)** 遵循 [Buchholz](https://en.wikipedia.org/wiki/Buchholz_psi_functions) 的定义  

$$
\Omega_n :=
\begin{cases}
   1 &\text{if } n = 0 \\
   \mathsf{lim}_{n'}(0_{n'},↑_+) &\text{if } n = n'^+
\end{cases}
$$

```agda
  Ω : (n : ℕ) → Ord n
  Ω zero    = suc zero
  Ω (suc n) = limᵢ zero ↑₊
```

继续往上, 与 $↑_+$ 类似地

**定义 (层级提升函数)** 对任意 $n : \mathbb{N}$, 递归定义 $\text{Ord}_n$ 到 $\text{Ord}_\omega$ 的嵌入 $↑_\omega$ 如下:  

$$
↑_\omega a :=
\begin{cases}
   \mathsf{zero} &\text{if } a = \mathsf{zero} \\
   \mathsf{suc}(↑_\omega a') &\text{if } a = \mathsf{suc}(a') \\
   \mathsf{lim}(↑_\omega \circ f) &\text{if } a = \mathsf{lim}(f) \\
   \mathsf{lim}_i(↑_\omega \circ f) &\text{if } a = \mathsf{lim}_i(p:i<n, f)
\end{cases}
$$

```agda
  ↑ω : Ord n → Ordω
  ↑ω zero = zero
  ↑ω (suc a) = suc (↑ω a)
  ↑ω (lim f) = lim (↑ω ∘ f)
  ↑ω (limᵢ p f) = limₙ _ (↑ω ∘ f ∘ coe₀)
```

由此, 对每个 $n$, 我们可以表达 $↑_ω : \text{Ord}_n\to\text{Ord}_\omega$ 的 $\mathsf{lim}_n$ 极限, 它们都是 $\text{Ord}_\omega$ 的内 $\Omega$ 数, 但都不是最大的那个. 在 $\text{Ord}_\omega$ 里可以取它们的 $\mathsf{lim}$ 极限, 得到的就是 $\text{Ord}_\omega$ 的最大内 $\Omega$ 数 $\Omega_\omega$.

**定义 ($\Omega_\omega$)** $\text{Ord}_\omega$ 的最大内 $\Omega$ 数定义为:  

$$
\Omega_\omega := \mathsf{lim}(n \mapsto \mathsf{lim}_n(↑_\omega))
$$

```agda
  Ωω : Ordω
  Ωω = lim (λ n → limₙ n ↑ω)
```

类似地可以定义 $\Omega_{\omega+n}$ 和 $\Omega_{\omega \cdot 2}$. 因为这些都会在后面由更一般化的定义给出, 这里就省略不写了.

目前的成果可以总结如下:

$$
\begin{array}{|c|c|c|c|}
\hline
\text{type} & \text{supermun} & \text{max inner }\Omega & \text{cofinality} \\
\hline
\mathbb{0} & 0 & \text{n/a} & \text{n/a} \\
\hline
\mathbb{1} & 1 & 0 & 0 \\
\hline
\mathbb{N} & \omega & 1 & 1 \\
\hline
\mathsf{Ord}_0 & \Omega & \omega & \omega \\
\hline
\mathsf{Ord}_1 & \Omega_2 & \Omega & \Omega \\
\hline
\mathsf{Ord}_2 & \Omega_3 & \Omega_2 & \Omega_2 \\
\hline
\mathsf{Ord}_n & \Omega_{n+1} & \Omega_n & \Omega_n \\
\hline
\mathsf{Ord}_{\omega} & \Omega_{\omega+1} & \Omega_\omega & \omega \\
\hline
\mathsf{Ord}_{\omega+1} & \Omega_{\omega+2} & \Omega_{\omega+1} & \Omega_{\omega+1} \\
\hline
\mathsf{Ord}_{\omega+n} & \Omega_{\omega+n+1} & \Omega_{\omega+n} & \Omega_{\omega+n} \\
\hline
\mathsf{Ord}_{\omega \cdot 2} & \Omega_{\omega \cdot 2+1} & \Omega_{\omega \cdot 2} & \omega \\
\hline
\mathsf{Ord}_{\omega \cdot 2+1} & \Omega_{\omega \cdot 2+2} & \Omega_{\omega \cdot 2+1} & \Omega_{\omega \cdot 2+1} \\
\hline
\end{array}
$$

## 可数序数的有界三歧性

为了一劳永逸地定义 $\mathsf{Ord}_\alpha$ (其中 $\alpha < \Omega$), 我们要以可数序数 $\mathsf{Ord}_0$ 为下标, 写出一个新的类型族 `Ord : Ord₀ → Set`. 但是我们现有的 `Ord₀` 太过于宽泛了, 缺乏一些关键性质, 不能直接作为索引类型, 否则会导致后续无法折叠. 为此我们将专门定义具有所谓**有界三歧性 (bounded decidability)** 的可数序数类型 $\mathsf{Ord}^\mathsf{D}$, 它也是我们在 [2.0系列](https://zhuanlan.zhihu.com/p/711649863) 介绍的良构序数的简化版本.

为了表达三歧性, 我们引入和类型.

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)
```

**引理** 在自然数上

- (1) 零小于后继
- (2) 后继运算保持小于关系

**证明**

(1) 要证 $0 < n^+$, 对 $n$ 归纳.

- 若 $n = 0$, 则 $0 < 0^+ = 1$, 由 $<$ 的定义 $\mathsf{zero}$ 直接得出.
- 若 $n = m^+$, 则要证 $0 < (m^+)^+ = m^{++}$. 由归纳假设 $0 < m^+$, 应用 $<$ 的构造子 $\mathsf{suc}$ 得 $0 < m^{++}$.

(2) 要证 $n < m \to n^+ < m^+$, 对 $n < m$ 的证明 $p$ 归纳.

- 若 $p = (0_n:n < n^+)$, 则要证 $n^+ < (n^+)^+ = n^{++}$, 由 $<$ 的定义 $\mathsf{zero}$ 直接得出.
- 若 $p = (p'^+:n < m^+)$, 其中 $p' : n < m$, 则要证 $n^+ < (m^+)^+ = m^{++}$. 由归纳假设得 $n^+ < m^+$, 应用构造子 $\mathsf{suc}$ 得 $n^+ < m^{++}$. ∎

```agda
module Trich where
  open Nat-Lt public

  z<s : ∀ n → zero < suc n
  z<s zero    = zero
  z<s (suc n) = suc (z<s n)

  s<s : n < m → suc n < suc m
  s<s zero    = zero
  s<s (suc p) = suc (s<s p)
```

**定理** 自然数的 $<$ 满足**无条件三歧性 (unconditional decidability)**, 即对任意 $n,m$, 都有 $(n < m) \lor (m < n) \lor (n = m)$.  
**证明** 对 $n,m$ 归纳.

- 若 $n=0,\;m=0$, 显然 $n=m$.
- 若 $n=0,\;m=m'^+$, 显然 $n<m$.
- 若 $n=n'^+,\;m=0$, 显然 $m<n$.
- 若 $n=n'^+,\;m=m'^+$, 有归纳假设 $n'<m'$ 或 $m'<n'$ 或 $n'=m'$, 讨论它们.

  - 如果 $n'<m'$, 则有 $n<m$.
  - 如果 $m'<n'$, 则有 $m<n$.
  - 如果 $n'=m'$, 则有 $n=m$. ∎

```agda
  <-dec : ∀ n m → n < m ⊎ m < n ⊎ n ≡ m
  <-dec zero zero = injᶜ refl
  <-dec zero (suc m) = injᵃ (z<s m)
  <-dec (suc n) zero = injᵇ (z<s n)
  <-dec (suc n) (suc m) with <-dec n m
  ... | injᵃ p = injᵃ (s<s p)
  ... | injᵇ p = injᵇ (s<s p)
  ... | injᶜ p = injᶜ (cong suc p)
```

**定义 (有界三歧可数序数)** 互归纳定义 $\mathsf{Ord}^\mathsf{D}$ 及其上的 $<$ 序.

- $\mathsf{Ord}^\mathsf{D}$ 的定义与 $\mathsf{Ord}_0$ 类似, 只不过要求基本列 $f:\mathbb{N}\to\mathsf{Ord}^\mathsf{D}$ 单调.
- $<$ 的定义在自然数的 $<$ 的基础上推广到了极限序数.

$$
\cfrac{a<f(n)}{\;a<\mathsf{lim}(f,m_f)\;}\;\;\mathsf{lim}
$$

其中

- $m_f$ 是 $f$ 的单调性证明, 通常省略不写.
- $f$ 的单调性是指: 对任意 $n,m:\mathbb{N}$, 如果 $n<m$, 那么 $f(n)<f(m)$. ∎

```agda
module BoundedTrich where
  open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)

  infix 10 _<_
  data Ordᴰ : Set
  data _<_ : Ordᴰ → Ordᴰ → Set

  monotonic : (ℕ → Ordᴰ) → Set
  monotonic f = ∀ {n m} → n <ᴺ m → f n < f m

  private variable
    a b c : Ordᴰ
    f :  ℕ → Ordᴰ
    mono : monotonic f

  data Ordᴰ where
    zero : Ordᴰ
    suc  : Ordᴰ → Ordᴰ
    lim  : (f : ℕ → Ordᴰ) (mono : monotonic f) → Ordᴰ

  data _<_ where
    zero : a < suc a
    suc  : a < b → a < suc b
    lim  : ∀ n → a < f n → a < lim f mono
```

**引理** 对任意单调的 $f:\mathbb{N}\to\mathsf{Ord}^\mathsf{D}$ 和 $n:\mathbb{N}$, 有 $f(n)<\mathsf{lim}(f)$.  
**证明** $f(n)<f(n^+)<\mathsf{lim}(f)$. ∎

```agda
  f<l : ∀ n → f n < lim f mono
  f<l {mono} n = lim (suc n) (mono zero)
```

**引理** $\mathsf{Ord}^\mathsf{D}$ 上的 $<$ 满足传递性.  
**证明** 令 $p:a<b$ 且 $q:b<c$, 要证 $a<c$. 对 $q$ 归纳.

- 若 $q=0$, 则有 $c=b^+$, 所以 $p^+:a<c$.
- 若 $q=q'^+$, 则有 $c=c'^+$ 且 $q':b<c'$. 此时有归纳假设 $ih:a<c'$, 所以 $ih^+:a<c$.
- 若 $q=\mathsf{lim}(n,q')$, 则有 $c=\mathsf{lim}(f,\_)$ 且 $q':b<f(n)$. 此时有归纳假设 $ih:a<f(n)$, 所以 $\mathsf{lim}(n,ih):a<c$. ∎

```agda
  <-trans : a < b → b < c → a < c
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
  <-trans p (lim n q) = lim n (<-trans p q)
```

**定理 (有界三歧性)** 对任意 $a,b:\mathsf{Ord}^\mathsf{D}$, 如果它们小于一个共同的序数, 那么它们满足三歧性.  
**证明** 令 $p:a<c$ 且 $q:b<c$, 对它们归纳.

- 若 $p=0,\;q=0$, 则 $c=a^+$ 且 $c=b^+$, 所以 $a=b$.
- 若 $p=0,\;q=q'^+$, 则 $c=a^+$, 此时 $q':b<a$.
- 若 $p=p'^+,\;q=0$, 则 $c=b^+$, 此时 $p':a<b$.
- 若 $p=\mathsf{lim}(n,p'),\;q=\mathsf{lim}(m,q')$, 则存在单调的 $f$ 使得 $c=\mathsf{lim}(f)$, 且有 $p':a<f(n),\;q':b<f(m)$. 由自然数的无条件三歧性, 讨论 $n,m$ 的大小关系.
  - 如果 $n<m$, 由 $f$ 的单调性有 $f(n)<f(m)$, 所以 $a,b$ 都小于 $f(m)$, 由归纳假设可知 $a,b$ 的大小关系.
  - 如果 $m<n$, 由 $f$ 的单调性有 $f(m)<f(n)$, 所以 $a,b$ 都小于 $f(n)$, 由归纳假设可知 $a,b$ 的大小关系.
  - 如果 $n=m$, 则 $a,b$ 都小于 $f(n) = f(m)$, 由归纳假设可知 $a,b$ 的大小关系. ∎

```agda
  <-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b
  <-dec zero zero       = injᶜ refl
  <-dec zero (suc q)    = injᵇ q
  <-dec (suc p) zero    = injᵃ p
  <-dec (suc p) (suc q) = <-dec p q
  <-dec (lim {mono} n p) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m  = <-dec (<-trans p (mono n<m)) q
  ... | injᵇ m<n  = <-dec p (<-trans q (mono m<n))
  ... | injᶜ refl = <-dec p q
```

达成 $\psi(\Omega_\Omega)$ 的关键是让 $\psi$ 输出的大可数序数成为 $\Omega$ 的下标, 从而迭代 $\psi(\Omega_x)$ 得到 $\psi(\Omega_\Omega)$. 问题在于, $\Omega$ 的下标的类型必须是我们现在构筑的 $\mathsf{Ord}^\mathsf{D}$, 而 $\psi$ 的输出并不是, 因为通常的 OCF 的定义并不保证输出的序数所用的基本列是“遗传地”单调的. 本小节接下来的构筑将提供此问题的一个简易的解决方案.

**定义 (可数序数加法)** 互递归地定义 $\mathsf{Ord}^\mathsf{D}$ 上的加法并证明右侧加法 ($x \mapsto a + x$) 保持 $<$ 关系.

$$
a + b := \begin{cases}
   a &\text{if } b=0 \\
   (a+b')^+ &\text{if } b=b'^+ \\
   \mathsf{lim}(n\mapsto a+f(n)) &\text{if } b=\mathsf{lim}(f)
\end{cases}
$$

其中 $n\mapsto a+f(n)$ 要求满足单调性, 因为有 $f$ 的单调性, 只要证 $x \mapsto a + x$ 保持 $<$ 关系即可.

**证明** 令 $p : b < c$, 对 $p$ 归纳.

- 若 $p = 0$, 则 $c = b^+$, 要证 $a + b < a + b^+ = (a + b)^+$, 应用 $\mathsf{zero}$ 即可.
- 若 $p = p'^+$, 则 $c = c'^+$ 且 $p' : b < c'$, 要证 $a + b < a + c^+ = (a + c')^+$. 由归纳假设 $a + b < a + c'$, 应用 $\mathsf{suc}$ 即可.
- 若 $p = \mathsf{lim}(n, p')$, 则 $c = \mathsf{lim}(f)$ 且 $p' : b < f(n)$, 要证 $a + b < a + \mathsf{lim}(f) = \mathsf{lim}(m \mapsto a + f(m))$. 由归纳假设 $a + b < a + f(n)$, 应用 $\mathsf{lim}$ 即可. ∎

```agda
  mutual
    _+_ : Ordᴰ → Ordᴰ → Ordᴰ
    a + zero          = a
    a + suc b         = suc (a + b)
    a + lim f f-mono  = lim (λ n → a + f n) (+-mono ∘ f-mono)

    +-mono : b < c → a + b < a + c
    +-mono zero       = zero
    +-mono (suc p)    = suc (+-mono p)
    +-mono (lim n p)  = lim n (+-mono p)
```

**引理** 如果 $a\neq 0$, 那么 $a>0$.  
**证明** 对 $a$ 归纳

- 若 $a = 0^+$, 则 $0_0:0<0^+$.
- 若 $a = a'^{++}$, 显然 $a'^+\neq 0$, 有归纳假设 $ih : 0 < a'^+$, 所以 $ih^+ : 0 < a'^{++}$.
- 若 $a = (\mathsf{lim}(f))^+$, 显然 $\mathsf{lim}(f)\neq 0$, 有归纳假设 $ih : 0 < \mathsf{lim}(f)$, 所以 $ih^+ : 0 < (\mathsf{lim}(f))^+$.
- 若 $a = \mathsf{lim}(f)$, 则由 $f$ 的单调性 $m_f$ 有 $m_f(0) : f(0) < f(1)$. 此时 $f(1) \neq 0$, 故由归纳假设 $ih : 0 < f(1)$, 因此 $\mathsf{lim}(1, ih) : 0 < \mathsf{lim}(f)$. ∎

```agda
  NonZero : Ordᴰ → Set
  NonZero zero = ⊥
  NonZero _    = ⊤

  sth<nz : a < b → NonZero b
  sth<nz zero       = _
  sth<nz (suc _)    = _
  sth<nz (lim _ _)  = _

  z<nz : NonZero a → zero < a
  z<nz {suc zero}         _ = zero
  z<nz {suc (suc a)}      _ = suc (z<nz _)
  z<nz {suc (lim f mono)} _ = suc (z<nz _)
  z<nz {lim f mono}       _ = lim 1 (z<nz (sth<nz (mono zero)))
```

**引理** 如果 $b \neq 0$, 那么 $a < a + b$.  
**证明** 由引理知若 $b \neq 0$ 则 $0 < b$, 再由加法保持 $<$ 关系即得 $a + 0 < a + b$, 即 $a < a + b$. ∎

```agda
  a<a+b : ⦃ _ : NonZero b ⦄ → a < a + b
  a<a+b = +-mono (z<nz it)
```

**定义 (累积和)** 定义高阶函数 $f\mapsto f^+$ 如下:  

$$
f^{+}(n) :=
\begin{cases}
   f(0) &\text{if } n = 0 \\
   f^{+}(m) + (f(n))^+ &\text{if } n = m^+
\end{cases}
$$

```agda
  -- cumulative sum
  cumsum : (ℕ → Ordᴰ) → (ℕ → Ordᴰ)
  cumsum f zero     = f zero
  cumsum f (suc n)  = cumsum f n + suc (f (suc n))
```

**定理** 对任意 $f$, $f^{+}$ 单调.  
**证明** 要证 $f^{+}$ 单调, 即对任意 $n < m$ 有 $f^{+}(n) < f^{+}(m)$. 对 $n < m$ 的证明归纳:

- 若 $n < n^+$, 要证 $f^{+}(n) < f^{+}(n^+) = f^{+}(n) + (f(n^+))^+$, 由引理 `a<a+b` 得证.
- 若 $n < m^+$ 且 $n < m$, 要证 $f^{+}(n) < f^{+}(m^+) = f^{+}(m) + (f(m^+))^+$. 由归纳假设 $f^{+}(n) < f^{+}(m)$, 再由传递性和引理 `a<a+b` 得证. ∎

```agda
  cumsum-mono : (f : ℕ → Ordᴰ) → monotonic (cumsum f)
  cumsum-mono f zero    = a<a+b
  cumsum-mono f (suc p) = <-trans (cumsum-mono f p) a<a+b
```

累积和可能会使某些基本列的极限值往上偏移, 但应该不改变我们对这套方法的最终极限的估值 ($\psi(\Omega_\Omega)$).

## 可数序数层布劳威尔树

现在我们将自然数层推广到可数序数层. 对任意可数序数 $\ell : \mathsf{Ord}^\mathsf{D}$, 我们定义布劳威尔树类型 $\mathsf{Ord}_\ell$.

**定义 (可数序数层布劳威尔树)**  

$$
\begin{align}
\mathsf{Ord}_+(\ell, \mathsf{Ord}_{<}) &:= 
\cfrac{}{\mathsf{Ord}_+}\;\mathsf{zero}
\;\;\;\;
\cfrac{\;\mathsf{Ord}_+\;}{\mathsf{Ord}_+}\;\mathsf{suc}
\;\;\;\;
\cfrac{\;\mathbb{N}\to\mathsf{Ord}_+\;}{\mathsf{Ord}_+}\;\mathsf{lim}
\\[1em]
&\;\;\;\;\cfrac{\;(p:i<\ell)\;\;\;(\mathsf{Ord}_{<}(i,p)\to\mathsf{Ord}_+)\;}{\mathsf{Ord}_+}\;\mathsf{lim}_i
\\[2em]
\mathsf{Ord}_{<}(i, p) &:= 
\begin{cases}
   \mathsf{Ord}_+(i, \mathsf{Ord}_{<}) &\text{if } p = (0_i:i<i^+) \\
   \mathsf{Ord}_{<}(i, q) &\text{if } p = (q^+:i<m^+) \\
   \mathsf{Ord}_{<}(i, q) &\text{if } p = (\mathsf{lim}(n,q):i<\mathsf{lim}(f))
\end{cases}
\\[2em]
\mathsf{Ord}_\ell &:= \mathsf{Ord}_{<}(\ell,0_\ell)
\end{align}
$$

```agda
module Ord-Ord where
  open BoundedTrich hiding (_+_)
  variable i ℓ ℓ₁ ℓ₂ : Ordᴰ

  module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
    data Ord₊ : Set where
      zero  : Ord₊
      suc   : Ord₊ → Ord₊
      lim   : (f : ℕ → Ord₊) → Ord₊
      limᵢ  : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊

  Ord< : (i : Ordᴰ) (p : i < ℓ) → Set
  Ord< i zero      = Ord₊ i Ord<
  Ord< i (suc p)   = Ord< i p
  Ord< i (lim n p) = Ord< i p

  Ord : Ordᴰ → Set
  Ord ℓ = Ord< ℓ zero

  Ord₀ : Set
  Ord₀ = Ord zero
```


这里 $\mathsf{Ord}_{<}(i, p)$ 的定义体现了**证明无关性 (proof irrelevance)**: 无论 $p$ 是如何证明 $i < \ell$ 的, 只要 $i$ 相同, 得到的类型都是一样的. 具体来说:

- 当 $p$ 是基础证明 $0_i:i<i^+$ 时, 我们得到 $\mathsf{Ord}_+(i, \mathsf{Ord}_{<})$
- 当 $p$ 是后继证明 $q^+:i<m^+$ 时, 我们"剥掉"外层的后继, 递归到 $\mathsf{Ord}_{<}(i, q)$
- 当 $p$ 是极限证明 $\mathsf{lim}(n,q):i<\mathsf{lim}(f)$ 时, 我们同样"剥掉"外层的极限, 递归到 $\mathsf{Ord}_{<}(i, q)$

最终所有证明都会被"剥掉"到基础情况, 因此 $\mathsf{Ord}_{<}(i, p)$ 实际上只依赖于 $i$, 而与具体的证明 $p$ 无关.

**定理** $\mathsf{Ord}_{<}(i,\;p:i<\ell_1)$ 与 $\mathsf{Ord}_{<}(i,\;q:i<\ell_2)$ 表示相同的树.  
**证明** 对证明 $p:i<\ell_1$ 和 $q:i<\ell_2$ 归纳. 由 $\mathsf{Ord}_{<}$ 的定义:

- 若 $p=(0_i:i<i^+),\;q=(0_i:i<i^+)$, 则 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_+(i, \mathsf{Ord}_{<}) = \mathsf{Ord}_{<}(i,q)$.
- 若 $p=(p'^+:i<\ell_1^+),\;q=(0_i:i<i^+)$, 则 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,p')$, 由归纳假设 $\mathsf{Ord}_{<}(i,p') = \mathsf{Ord}_{<}(i,q)$.
- 若 $p=(\mathsf{lim}(n,p'):i<\mathsf{lim}(f)),\;q=(0_i:i<i^+)$, 则 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,p')$, 由归纳假设 $\mathsf{Ord}_{<}(i,p') = \mathsf{Ord}_{<}(i,q)$.
- 若 $p:i<\ell_1,\;q=q'^+:i<\ell_2^+$, 则 $\mathsf{Ord}_{<}(i,q) = \mathsf{Ord}_{<}(i,q')$, 由归纳假设直接得 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,q')$.
- 若 $p:i<\ell_1,\;q=\mathsf{lim}(n,q'):i<\mathsf{lim}(g)$, 则 $\mathsf{Ord}_{<}(i,q) = \mathsf{Ord}_{<}(i,q')$, 由归纳假设直接得 $\mathsf{Ord}_{<}(i,p) = \mathsf{Ord}_{<}(i,q')$. ∎

```agda
  Ord<-≡ : (p : i < ℓ₁) (q : i < ℓ₂) → Ord< i p ≡ Ord< i q
  Ord<-≡ zero zero      = refl
  Ord<-≡ (suc p) zero   = Ord<-≡ p zero
  Ord<-≡ (lim n p) zero = Ord<-≡ p zero
  Ord<-≡ p (suc q)      = Ord<-≡ p q
  Ord<-≡ p (lim n q)    = Ord<-≡ p q
```

也就是说 $\mathsf{Ord}_{<}(i,\;p:i<\ell)$ 与 $p$ 和 $\ell$ 无关, 我们改记作 $\mathsf{Ord}_{<i<\_}$.

```agda
  coe : {p : i < ℓ₁} {q : i < ℓ₂} → Ord< i p → Ord< i q
  coe {p} {q} = transport (Ord<-≡ p q)

  coe₀ : {p : i < ℓ₂} → Ord i → Ord< i p
  coe₀ = coe {p = zero}
```

**定义 (层级提升函数)** 给定证明 $p:\ell_1<\ell_2$, 递归定义 $\mathsf{Ord}_{\ell_1}$ 到 $\mathsf{Ord}_{\ell_2}$ 的嵌入 $\uparrow_p$ 如下:  

$$
\uparrow_p a :=
\begin{cases}
   0 &\text{if } a = 0 \\
   (\uparrow_p a')^+ &\text{if } a = a'^+ \\
   \mathsf{lim}(\uparrow_p \circ f) &\text{if } a = \mathsf{lim}(f) \\
   \mathsf{lim}_i(r:i<\ell_2, \uparrow_p \circ f) &\text{if } a = \mathsf{lim}_i(q:i<\ell_1, f)
\end{cases}
$$

其中 $r:i<\ell_2$ 由 $p,q$ 和 $<$ 的传递性得到.

```agda
  ↑ : ℓ₁ < ℓ₂ → Ord ℓ₁ → Ord ℓ₂
  ↑ p zero        = zero
  ↑ p (suc a)     = suc (↑ p a)
  ↑ p (lim f)     = lim (↑ p ∘ f)
  ↑ p (limᵢ q f)  = limᵢ (<-trans q p) (↑ p ∘ f ∘ coe)
```

**定义 ($\Omega$ 数)** 遵循 [Buchholz](https://en.wikipedia.org/wiki/Buchholz_psi_functions) 的定义, 对任意层级 $\ell:\mathsf{Ord}^\mathsf{D}$, 递归定义 $\Omega:\mathsf{Ord}^\mathsf{D}\to\mathsf{Ord}_\ell$ 如下:  

$$
\Omega_\ell :=
\begin{cases}
   \omega &\text{if } \ell = 0 \\
   \mathsf{lim}_{\ell'}(0_{\ell'}, \uparrow_{0_{\ell'}}) &\text{if } \ell = \ell'^+ \\
   \mathsf{lim}(n\mapsto\uparrow_{p:f(n)<\ell} \Omega_{f(n)}) &\text{if } \ell = \mathsf{lim}(f, \_)
\end{cases}
$$

其中 $p:f(n)<\ell$ 由引理 `f<l` 得到.

```agda
  ω : Ord zero
  ω = lim suc-iter
    where
      suc-iter : ℕ → Ord zero
      suc-iter zero    = zero
      suc-iter (suc n) = suc (suc-iter n)

  Ω : (ℓ : Ordᴰ) → Ord ℓ
  Ω zero      = ω
  Ω (suc ℓ)   = limᵢ zero (↑ zero)
  Ω (lim f _) = lim (λ n → ↑ (f<l n) (Ω (f n)))
```

## 布劳威尔树的折叠

**定义 (序数加法)** 对任意 $a,b:\mathsf{Ord}_\ell$, 递归定义加法运算 $+:\mathsf{Ord}_\ell\to\mathsf{Ord}_\ell\to\mathsf{Ord}_\ell$ 如下:  

$$
a + b :=
\begin{cases}
   a &\text{if } b = 0 \\
   (a + b')^+ &\text{if } b = b'^+ \\
   \mathsf{lim}(n \mapsto a + f(n)) &\text{if } b = \mathsf{lim}(f) \\
   \mathsf{lim}_i(p, x \mapsto a + f(x)) &\text{if } b = \mathsf{lim}_i(p, f)
\end{cases}
$$

```agda
  _+_ : Ord ℓ → Ord ℓ → Ord ℓ
  a + zero = a
  a + suc b = suc (a + b)
  a + lim f = lim (λ n → a + f n)
  a + limᵢ p f = limᵢ p (λ x → a + f x)
```

**定义 (迭代和最小不动点)** 定义迭代函数 $(f,a,n)\mapsto f^n(a)$ 和最小不动点构造 $g \mapsto \mathsf{lfp}(g)$ 如下:  

$$
\begin{align}
f^n(a) &:=
\begin{cases}
   a &\text{if } n = 0 \\
   f(f^{n'}(a)) &\text{if } n = n'^+
\end{cases}\\[2em]
\mathsf{lfp}(g) &:= \mathsf{lim}(n \mapsto g^n(0))
\end{align}
$$

```agda
  iter : {T : Set} (f : T → T) (init : T) (times : ℕ) → T
  iter f a zero    = a
  iter f a (suc n) = f (iter f a n)

  lfp : (Ord ℓ → Ord ℓ) → Ord ℓ
  lfp f = lim (iter f zero)
```

**定义 (Buchholz's $\psi_i$)** 给定证明 $p:i<\ell$, 递归定义序数折叠函数 $\psi_{p}:\mathsf{Ord}_\ell\to\mathsf{Ord}_i$ 如下:  

$$
\psi_{p}(a) :=
\begin{cases}
   \Omega_i &\text{if } a = 0 \\
   \mathsf{lfp}(x\mapsto\psi_{p}(a') + x) &\text{if } a = a'^+ \\
   \mathsf{lim}(\psi_{p} \circ f)) &\text{if } a = \mathsf{lim}(f) \\
   \begin{cases}
      \mathsf{lim}_j(q,\;\psi_{p} \circ f) &\text{if } r:j < i \\
      \mathsf{lfp}(\psi_{p} \circ f \circ \uparrow_{r}) &\text{if } r:i < j \\
      \mathsf{lfp}(\psi_{p} \circ f) &\text{if } r:i = j
   \end{cases} &\text{if } a = \mathsf{lim}_j(q:j<\ell, f)
\end{cases}
$$

其中, 我们能判定 $i,j$ 的大小关系是因为它们都小于 $\ell$, 允许应用有界三歧性.

```agda
  -- Buchholz's ψ
  ψ< : i < ℓ → Ord ℓ → Ord i
  ψ< p zero     = Ω _
  ψ< p (suc a)  = lfp (ψ< p a +_)
  ψ< p (lim f)  = lim (ψ< p ∘ f)
  ψ< {i} {ℓ} p (limᵢ {i = j} q f) with <-dec q p
  ... | injᵃ j<i  = limᵢ j<i (ψ< p ∘ f ∘ coe)
  ... | injᵇ i<j  = lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)
  ... | injᶜ refl = lfp (ψ< p ∘ f ∘ coe₀)
```

**定义 (Buchholz's $\psi_0$)** 递归定义 $\psi_0:\mathsf{Ord}_\ell\to\mathsf{Ord}_0$ 如下:  

$$
\psi_0(a) :=
\begin{cases}
   a &\text{if } \ell = 0 \\
   \psi_0(\psi_{0_{\ell'}}(a)) &\text{if } \ell = \ell'^+ \\
   \mathsf{lim}(n \mapsto \psi_0(\psi_{p}(a))) &\text{if } \ell = \mathsf{lim}(f, \_)
\end{cases}
$$

其中 $p:f(n)<\ell$ 由引理 `f<l` 得到.

```agda
  ψ₀ : Ord ℓ → Ord₀
  ψ₀ {ℓ = zero}    a = a
  ψ₀ {ℓ = suc ℓ}   a = ψ₀ (ψ< zero a)
  ψ₀ {ℓ = lim f _} a = lim (λ n → ψ₀ (ψ< (f<l n) a))
```

**定义 (单调化嵌入)** 递归定义 $\mathsf{Ord}_0$ 到 $\mathsf{Ord}^\mathsf{D}$ 的嵌入 $\mathsf{ord}^\mathsf{D}:\mathsf{Ord}_0\to\mathsf{Ord}^\mathsf{D}$ 如下:  

$$
\mathsf{ord}^\mathsf{D}(a) :=
\begin{cases}
   0 &\text{if } a = 0 \\
   (\mathsf{ord}^\mathsf{D}(a'))^+ &\text{if } a = a'^+ \\
   \mathsf{lim}((\mathsf{ord}^\mathsf{D}\circ f)^+, m_{(\mathsf{ord}^\mathsf{D}\circ f)^+}) &\text{if } a = \mathsf{lim}(f)
\end{cases}
$$

其中 $m_{(\mathsf{ord}^\mathsf{D}\circ f)^+}$ 由引理 `cumsum-mono` 给出.

```agda
  ordᴰ : Ord₀ → Ordᴰ
  ordᴰ zero     = zero
  ordᴰ (suc a)  = suc (ordᴰ a)
  ordᴰ (lim f)  = lim (cumsum (ordᴰ ∘ f)) (cumsum-mono (ordᴰ ∘ f))
```

**定义 (迭代 $\psi_0$)** 定义 $\psi^n:\mathbb{N}\to\mathsf{Ord}_0$ 为 $\psi_0 \circ \Omega \circ \mathsf{ord}^\mathsf{D}$ 的 $n$ 次迭代:  

$$
\psi^n(0) := (\psi_0 \circ \Omega \circ \mathsf{ord}^\mathsf{D})^n(0)
$$

```agda
  -- n-iteration of ψ₀(Ω_x)
  ψⁿ : ℕ → Ord₀
  ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero
```

**例 (关键序数)**  

$$
\begin{align}
\psi^0(0) &= 0 \\
\psi^1(0) &= \omega \\
\psi^2(0) &= \psi(\Omega_\omega) = \mathsf{BO} \\
\psi^3(0) &= \psi(\Omega_{\mathsf{BO}}) \\
\psi^4(0) &= \psi(\Omega_{\psi(\Omega_{\mathsf{BO}})})
\end{align}
$$

```agda
  ex0 : ψⁿ 0 ≡ zero
  ex0 = refl

  ex1 : ψⁿ 1 ≡ ω
  ex1 = refl

  ex2 = ψⁿ 2  -- ψ(Ω_ω) = Buchholz's ordinal
  ex3 = ψⁿ 3  -- ψ(Ω_BO)
  ex4 = ψⁿ 4  -- ψ(Ω_ψ(Ω_BO))
```

**定义 (布劳威尔树壁垒序数)**  

$$
\mathsf{BTBO} := \mathsf{lim}(n\mapsto\psi^n(0)) = \psi(\Omega_\Omega)
$$

这是 $\psi^n(0)$ 序列的极限, 也就是我们能达到的最大序数 $\psi(\Omega_\Omega)$.

```agda
  -- Brouwer tree barrier ordinal
  BTBO : Ord₀
  BTBO = lim ψⁿ -- ψ(Ω_Ω)
```

最后, 遵循传统, 我们写出大数.

**定义 (快速增长层级)** 递归定义 $\mathbf{f}:\mathsf{Ord}_0\to\mathbb{N}\to\mathbb{N}$ 如下:  

$$
\mathbf{f}_\alpha(n) :=
\begin{cases}
   n^+ &\text{if } \alpha = 0 \\
   (\mathbf{f}_{\alpha'})^n(n) &\text{if } \alpha = \alpha'^+ \\
   \mathbf{f}_{f(n)}(n) &\text{if } \alpha = \mathsf{lim}(f)
\end{cases}
$$

```agda
  FGH : Ord₀ → ℕ → ℕ
  FGH zero    n = suc n
  FGH (suc a) n = iter (FGH a) n n
  FGH (lim a) n = FGH (a n) n
```

**定义 (BTBO大数)** 应用快速增长层级于 BTBO:  

$$
\mathbf{f}_\mathsf{BTBO}(99)
$$

这是一个基于布劳威尔树壁垒序数的具体大数.

```agda
  _ : ℕ
  _ = FGH BTBO 99
```

## 参考

- [Andras Kovacs - Large countable ordinals and numbers in Agda](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a?permalink_comment_id=5617267)
- [ccz181078 - googology](https://github.com/ccz181078/googology)
- [Thierry Coquand - Inductive Definitions and Constructive Mathematics](https://www.cse.chalmers.se/~coquand/prague1.pdf)
- [Googology Wiki - Ordinal collapsing function](https://googology.fandom.com/wiki/Ordinal_collapsing_function)
- [ユーザーブログ:Hexirp - ブラウワー順序数の制限と拡張](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/ブラウワー順序数の制限と拡張)
- [ユーザーブログ:Hexirp - 2024-12-25 のメモ](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/2024-12-25_のメモ)

## 附录

[ccz181078](https://github.com/ccz181078) 使用[另一种类似的方法](https://github.com/ccz181078/googology/blob/main/BuchholzOCF.v) 实现了 $\mathsf{Ord}_n$, 但似乎更难以往上推广. 我们给出该方法的 Agda 版本, 以供参考.

```agda
module Ord-Nat-ccz181078 where
  open Ord-Basic

  -- 假设某 `X = Ordₙ` 已完成, 并且已知任意 `x : X` 的共尾度 `cf x`
  module _ {X : Set} (cf : X → Set) where
    -- 定义 Ordₙ₊₁, 将其共尾度划分为5类: 0, 1, ω, (ω, Ω), Ω
    data Ord₊ : Set where
      zero : Ord₊
      suc : Ord₊ → Ord₊
      limω : (f : ℕ → Ord₊) → Ord₊
      -- 代表所有 `k≤n` 的 `Ordₖ` 的 `limΩ`.
      limX : (x : X) (f : cf x → Ord₊) → Ord₊
      limΩ : (f : X → Ord₊) → Ord₊

    -- 定义 `α : Ordₙ₊₁` 的共尾度
    cf₊ : Ord₊ → Set
    cf₊ (limΩ _) = X
    cf₊ (limX x _) = cf x
    -- 我们只关心 >ω 的情况
    cf₊ _ = ⊤

  -- 互递归完成下标为自然数的整个 `Ordₙ` 层级以及每层的共尾度
  mutual
    Ord : ℕ → Set
    Ord zero = Ord₀
    Ord (suc n) = Ord₊ (cf n)

    cf : (n : ℕ) → Ord n → Set
    cf zero _ = ⊤
    cf (suc n) = cf₊ (cf n)
```
