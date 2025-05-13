# 树序数大数计划综述

我们主张的树序数大数计划基于以下纲领:

1. 序数先行
   - 即先实现序数再折叠成大数
   - 排除了很难分析序数上下界的函数以及非序数增长率函数
2. 理想计算机可运行
   - 在以类型论为基础的证明助理中无公理地写出定义
3. 保证停机
   - 通过证明助理的自动停机检查器保证停机

本文介绍了该计划的总体思路, 当前的进展, 以及遇到的困难.

```agda
module OCF.Roadmap where
```

## 什么是树序数

首先, 从零开始 (字面意义), 我们能看得跟清晰一些.

```agda
module Tree_literal where

  data 𝟘 : Set where

  data 𝟙 : Set where
    zero : (𝟘 → 𝟙) → 𝟙

  data ℕ : Set where
    zero : (𝟘 → ℕ) → ℕ
    suc : (𝟙 → ℕ) → ℕ

  data 𝕎₁ : Set where
    zero : (𝟘 → 𝕎₁) → 𝕎₁
    suc : (𝟙 → 𝕎₁) → 𝕎₁
    lim : (ℕ → 𝕎₁) → 𝕎₁

  data 𝕎₂ : Set where
    zero : (𝟘 → 𝕎₂) → 𝕎₂
    suc : (𝟙 → 𝕎₂) → 𝕎₂
    lim : (ℕ → 𝕎₂) → 𝕎₂
    lim₁ : (𝕎₁ → 𝕎₂) → 𝕎₂
```

不难看出这里的

`𝟘`, `𝟙`, `ℕ`, `𝕎₁`, `𝕎₂`, ...

所能表示的序数的上确界 (记作 $\sup$) 为

$$0, 1, \omega, \omega_1, \omega_2, ...$$

把 `𝟘`, `𝟙`, `ℕ`, `𝕎₁`, `𝕎₂`, ... 重命名为 $\texttt{Tree}_\alpha$, 使得

$$
\begin{align}
\sup(\texttt{Tree}_0) &= 0 \\
\sup(\texttt{Tree}_1) &= 1 \\
\sup(\texttt{Tree}_2) &= \omega \\
\sup(\texttt{Tree}_3) &= \omega_1 \\
\sup(\texttt{Tree}_4) &= \omega_2 \\
...
\end{align}
$$

当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

不难看出 $\texttt{Tree}_1$ 到 $\texttt{Tree}_0$ 以及 $\texttt{Tree}_2$ 到 $\texttt{Tree}_1$ 的折叠是平凡的.

而 $\texttt{Tree}_3$ 到 $\texttt{Tree}_2$ 的折叠就是各种增长层级.

再往后的折叠就是通常所说的 OCF. 只不过通常的定义是非直谓的, 通过一个抽象的定义从某个很大的 $\texttt{Tree}_\alpha$ 一步折叠到 $\texttt{Tree}_3$, 而我们这里需要具体的递归算法一层一层往下: $\texttt{Tree}_\alpha$ 到 ... 到 $\texttt{Tree}_4$ 到 $\texttt{Tree}_3$ (大可数序数) 到 $\texttt{Tree}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Tree}_\alpha$, 二是一层层折叠到 $\texttt{Tree}_2$.

只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一很多附加的要求, 导致很大的 $\texttt{Tree}_\alpha$ 也难以实现. 我们一步步看.

## 任务一: $\Omega_{\Omega_{._{._.}}}$的实现路径

首先由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Tree}_{<\omega}$. 伪代码如下

```pseudocode
data Treeₖ₊₁ : Set where
  seq₀ : (Tree₀ → Treeₖ₊₁) → Treeₖ₊₁
  seq₁ : (Tree₁ → Treeₖ₊₁) → Treeₖ₊₁
  ...
  seqₖ : (Treeₖ → Treeₖ₊₁) → Treeₖ₊₁
```

其中下标 `k + 1` 代表了不同构造子的个数, 而下标为 `k` 的构造子则构造了以 `Treeₖ` 为长度的基本列.

- `seq₀` 构造了长度为 $\texttt{Tree}_0 = 0$ 的基本列, 它只有一个, 就是空列 `λ ()`, 代表序数 $0$
- `seq₁` 构造了长度为 $\texttt{Tree}_1 = 1$ 的基本列, 代表了该基本列的唯一元素的后继.
- `seq₂` 构造了长度为 $\texttt{Tree}_2 = \omega$ 的基本列, 代表基本列的极限.
- `seq₃` 构造了长度为 $\texttt{Tree}_3 = \omega_1$ 的基本列, 代表更高阶的极限.
- ...

归纳这个模式, 稍微使用一些类型宇宙的技巧我们可以写出 `Treeω : ℕ → Set` 这个类型族.

```agda
module Tree_omega where
  -- 不难证明开篇代码定义的 `ℕ` 与标准库的 `ℕ` 同构, 方便起见直接从库中导入.
  open import Data.Nat hiding (_<_)

  -- 方便起见, 序采用以下定义
  data _<_ : ℕ → ℕ → Set where
    base : ∀ {n} → n < suc n
    step  : ∀ {n m} → n < m → n < suc m

  -- 假设所有 `k < n` 层已经定义完成, 定义第 `n` 层
  data U (n : ℕ) (E : ∀ k → k < n → Set) : Set where
    -- `Treeₙ` 的元素由那些长度为 `Tree₀`, `Tree₁`, ... `Treeₖ` 的基本列构成
    seq : (k : ℕ) (p : k < n) (a : E k p → U n E) → U n E

  -- 递归完成所有 `k < n` 层的定义
  Elm : ∀ n k → k < n → Set
  Elm (suc k) k base = U k (Elm k)
  Elm (suc n) k (step p) = Elm n k p

  -- 完成以自然数为下标的 `Treeω` 层级
  Treeω : ℕ → Set
  Treeω n = U n (Elm n)
```

我们认为 `Treeω : ℕ → Set` 这个类型族形式化了 $\texttt{Tree}_\omega$. 也就是说, 我们认为

- 当 $\alpha$ 为后继时, $\texttt{Tree}_\alpha$ 是一个类型, 且有 $\text{cf}(\sup(\texttt{Tree}_\alpha)) = \sup(\texttt{Tree}_\alpha)$
- 当 $\alpha$ 为极限时, $\texttt{Tree}_\alpha$ 是一个类型族, 且有 $\text{cf}(\sup(\texttt{Tree}_\alpha)) = \sup(\text{idx}(\texttt{Tree}_\alpha))$

其中 $\text{cf}$ 表示共尾度, $\text{idx}$ 表示类型族的索引类型.

为了对齐下标我们引入 $\texttt{Ord}$ 的记法

$$
\begin{align}
\texttt{Ord}_1 &:= \texttt{Tree}_3 \\
\texttt{Ord}_2 &:= \texttt{Tree}_4 \\
... \\
\texttt{Ord}_\omega &:= \texttt{Tree}_\omega \\
\end{align}
$$

其中 $\texttt{Ord}_1$ 又简记作 $\texttt{Ord}$, 它是可数序数的类型.

并且引入传统记法 $\Omega$

$$
\begin{align}
\Omega_1 &:= \omega_1 \\
\Omega_2 &:= \omega_2 \\
\Omega_3 &:= \omega_3 \\
...
\end{align}
$$

其中 $\Omega_1$ 又简记作 $\Omega$, 它是可数序数的极限.

即有

$$
\sup(\texttt{Ord}) = \Omega
$$

乃至

$$
\sup(\texttt{Ord}_\alpha) = \Omega_\alpha
$$

上一个代码块我们以 `ℕ` 为下标, 写出了 `Treeω`, 它形式化了 $\texttt{Ord}_{\omega}$, 满足

$$
\sup(\texttt{Ord}_\omega) = \Omega_\omega
$$

继续往上, 很明显了, 我们要以 `Treeω 3`, 也即 $\texttt{Ord}$ 为下标, 写出一个新的类型族 `OrdΩ : Treeω 3 → Set`. 具体方法参考 Andras Kovacs 的 [Gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 中的 `U`. 它形式化了 $\texttt{Ord}_\Omega$, 上确界为 $\Omega_{\Omega}$. Andras Kovacs 用它写出了 $\psi(\Omega_{\varepsilon_0}) = \text{PTO}(\text{ID}_{<\varepsilon_0})$, 其中 $\psi$ 是 [Madore 的 $\psi$](https://googology.fandom.com/wiki/Madore%27s_function), 但扩张到了 $\Omega$ 多个 $\Omega$.

以此类推, 我们有

|类型族|索引类型|共尾度|上确界|
|-|-|-|-|
|$\texttt{Ord}_\omega$|$\N$|$\omega$|$\Omega_{ \omega}$|
|$\texttt{Ord}_\Omega$|$\texttt{Ord}$|$\omega_1$|$\Omega_{ \Omega}$|
|$\texttt{Ord}_{\Omega_2}$|$\texttt{Ord}_2$|$\omega_2$|$\Omega_{\Omega_2}$|
|...|...|...|...|
|$\texttt{Ord}_{\Omega_\omega}$|$\N,\texttt{Ord}_\omega$|$\omega$|$\Omega_{\Omega_\omega}$|
|$\texttt{Ord}_{\Omega_{\Omega_\omega}}$|$\N,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega}$|$\omega$|$\Omega_{\Omega_\omega}$|
|...|...|...|...|
|$\texttt{Ord}_{\Lambda}$|$\N,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega},...$|$\omega$|$\Omega_{\Omega_{._{._.}}}$|

其中最后三行可能将具有以下类型

```agda
module Ord_Omega_fixpoint where
  open import Data.Nat
  open Tree_omega renaming (Treeω to Ordω)
  postulate
    OrdΩω : (n : ℕ) → Ordω n → Set
    OrdΩΩω : (n : ℕ) (α : Ordω n) → OrdΩω n α → Set
    OrdΛ : ℕ → Set
```

我们还没有研究它们的具体实现, 因为 $\texttt{Ord}_{\Omega_2}$ 的折叠就已经遇到了困难.

## 任务二: $\Omega$数的折叠

回顾前文

- $\texttt{Tree}_1$ 到 $\texttt{Tree}_0$ 的折叠是平凡的
- $\texttt{Tree}_2$ 到 $\texttt{Tree}_1$ 的折叠是平凡的
- $\texttt{Tree}_3$ 到 $\texttt{Tree}_2$ 的折叠就是各种增长层级
- 再往后的折叠就是通常所说的 OCF

### 最初几层的折叠

```agda
module NaiveCollapsing where
  open import Data.Nat

  data Ord : Set where
    zero : Ord
    suc : Ord → Ord
    lim : (ℕ → Ord) → Ord

  data Ord₂ : Set where
    zero : Ord₂
    suc : Ord₂ → Ord₂
    lim : (ℕ → Ord₂) → Ord₂
    Lim : (Ord → Ord₂) → Ord₂
```

### BO, TFBO, 及其上不远的位置

## 为什么 $\Omega_{\Omega_2}$ 的折叠是困难的

“自下而上使用相同基本列”这个意义下的真前段
