# 树序数大数计划综述

我们主张的树序数大数计划基于以下纲领:

1. 遵循序数的指引
  - 即先实现序数再实现以该序数为增长率的函数
  - 而不是先实现函数, 再分析其增长率上下界, 或者非序数增长率函数
2. 可运行于理想的计算机中
  - 实践上可以选择在以类型论为基础的证明助理中无公理地写出定义
3. 保证停机
  - 实践上可以通过证明助理的自动停机检查器保证

本文介绍了该计划的总体思路, 当前的进展, 以及遇到的困难.

```agda
module OCF.Roadmap where
```

## 什么是树序数

首先, 从零开始 (字面意义), 我们能看得跟清晰一些.

```agda
module Ord_literal where

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

正好对应了共尾度

$$0, 1, \omega, \omega_1, \omega_2, ...$$

(可以认为0不是共尾度不过这无关紧要)

我们把它们重命名为 $\texttt{Ord}_\alpha$

$$
\begin{align}
\texttt{Ord}_0 &:= 0 \\
\texttt{Ord}_1 &:= 1 \\
\texttt{Ord}_2 &:= \omega \\
\texttt{Ord}_3 &:= \omega_1 \\
\texttt{Ord}_4 &:= \omega_2 \\
\end{align}
$$

当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

不难看出 $\texttt{Ord}_1$ 到 $\texttt{Ord}_0$ 以及 $\texttt{Ord}_2$ 到 $\texttt{Ord}_1$ 的折叠是平凡的.

而 $\texttt{Ord}_3$ 到 $\texttt{Ord}_2$ 的折叠就是各种增长层级.

再往后的折叠就是通常所说的 OCF. 只不过通常的定义是非直谓的, 通过一个抽象的定义从某个很大的 $\texttt{Ord}_\alpha$ 一步折叠到 $\texttt{Ord}_3$, 而我们这里需要具体的递归算法一层一层往下: $\texttt{Ord}_\alpha$ 到 ... 到 $\texttt{Ord}_4$ 到 $\texttt{Ord}_3$ (大可数序数) 到 $\texttt{Ord}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Ord}_\alpha$, 二是一层层折叠到 $\texttt{Ord}_2$.

只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一很多附加的要求, 导致很大的 $\texttt{Ord}_\alpha$ 也难以实现. 我们一步步看.

## Ω不动点

首先由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Ord}_{<\omega}$. 伪代码如下

```pseudocode
data Ordₖ₊₁ : Set where
  seq₀ : (Ord₀ → Ordₖ₊₁) → Ordₖ₊₁
  seq₁ : (Ord₁ → Ordₖ₊₁) → Ordₖ₊₁
  ...
  seqₖ : (Ordₖ → Ordₖ₊₁) → Ordₖ₊₁
```

其中下标 `k + 1` 代表了不同构造子的个数, 而下标为 `k` 的构造子则构造了以 `Ordₖ` 为长度的基本列.

- `seq₀` 构造了长度为 $\texttt{Ord}_0 = 0$ 的基本列, 它只有一个, 就是空列 `λ ()`, 代表序数 $0$
- `seq₁` 构造了长度为 $\texttt{Ord}_1 = 1$ 的基本列, 代表了该基本列的唯一元素的后继.
- `seq₂` 构造了长度为 $\texttt{Ord}_2 = \omega$ 的基本列, 代表基本列的极限.
- `seq₃` 构造了长度为 $\texttt{Ord}_3 = \omega_1$ 的基本列, 代表更高阶的极限.
- ...

归纳这个模式, 稍微使用一些类型宇宙的技巧我们可以写出 `Ordω : ℕ → Set` 这个类型族.

```agda
module Ord_omega where
  -- 不难证明开篇代码定义的 `ℕ` 与标准库的 `ℕ` 同构, 方便起见直接从库中导入.
  open import Data.Nat hiding (_<_)

  -- 方便起见, 序采用以下定义
  data _<_ : ℕ → ℕ → Set where
    base : ∀ {n} → n < suc n
    step  : ∀ {n m} → n < m → n < suc m

  -- 假设所有 `k < n` 层已经定义完成, 定义第 `n` 层
  data U (n : ℕ) (E : ∀ k → k < n → Set) : Set where
    -- `Ordₙ` 的元素由那些长度为 `Ord₀`, `Ord₁`, ... `Ordₖ` 的基本列构成
    seq : (k : ℕ) (p : k < n) (a : E k p → U n E) → U n E

  -- 递归完成所有 `k < n` 层的定义
  Elm : ∀ n k → k < n → Set
  Elm (suc k) k base = U k (Elm k)
  Elm (suc n) k (step p) = Elm n k p

  -- 完成以自然数为下标的 `Ordω` 层级
  Ordω : ℕ → Set
  Ordω n = U n (Elm n)
```

我们认为 `Ordω : ℕ → Set` 这个类型族形式化了 $\texttt{Ord}_\omega$. 也就是说, 我们认为

- 当 $\alpha$ 为后继时, $\texttt{Ord}_\alpha$ 是一个类型, 其共尾度为 $1$
- 当 $\alpha$ 为极限时, $\texttt{Ord}_\alpha$ 是一个类型族, 索引类型就是其共尾度

现在引入传统记法 $\Omega$. 虽然 $\texttt{Ord}_\omega$ 跟 $\Omega$ 的下标没有完全对齐, 即有

$$
\begin{align}
\texttt{Ord}_3 &= \Omega \\
\texttt{Ord}_4 &= \Omega_1 \\
\texttt{Ord}_5 &= \Omega_2 \\
\end{align}
$$

但 $\texttt{Ord}_\omega$ 凌驾于 $\Omega_n$, 上确界为 $\Omega_{\omega}$. 在这层意义上我们说 $\texttt{Ord}_\omega$ 实现了 $\Omega_{\omega}$.

继续往上, 很明显了, 我们要以 $\texttt{Ord}_3 = \Omega$ 为下标, 写出一个新的类型族 `OrdΩ : Ord₃ → Set`. 具体方法参考 Andras Kovacs 的 [Gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a). 它形式化了 $\texttt{Ord}_\Omega$, 上确界为 $\Omega_{\Omega}$, 凌驾于 $\Omega_\omega$. Andras Kovacs 用它写出了 $\psi(\Omega_{\varepsilon_0}) = \text{PTO}(\text{ID}_{<\varepsilon_0})$

以此类推, 我们有

|类型族|索引类型|共尾度|上确界|凌驾|
|-|-|-|-|-|
|$\texttt{Ord}_\omega$|$\texttt{Ord}_2$|$\omega$|$\Omega_{ \omega}$|$\Omega_n$|
|$\texttt{Ord}_\Omega$|$\texttt{Ord}_3$|$\omega_1$|$\Omega_{ \Omega}$|$\Omega_{\omega}$|
|$\texttt{Ord}_{\Omega_1}$|$\texttt{Ord}_4$|$\omega_2$|$\Omega_{\Omega_1}$|$\Omega_{\Omega}$|
|...|...|...|...|...|
|$\texttt{Ord}_{\Omega_\omega}$|$\texttt{Ord}_2,\texttt{Ord}_\omega$|$\omega$|$\Omega_{\Omega_\omega}$|$\Omega_{\Omega_n}$|
|$\texttt{Ord}_{\Omega_{\Omega_\omega}}$|$\texttt{Ord}_2,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega}$|$\omega$|$\Omega_{\Omega_\omega}$|$\Omega_{\Omega_n}$|
|...|...|...|...|...|
|$\texttt{Ord}_{\Lambda}$|$\texttt{Ord}_2,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega},...$|$\omega$|$\Omega_{\Omega_{._{._.}}}$|$\Omega_{\Omega_{._{._{._{\Omega_n}}}}}$|

其中最后三行将具有以下类型

```agda
module Ord_Omega_fixpoint where
  open import Data.Nat
  open Ord_omega using (Ordω)
  postulate
    OrdΩω : (n : ℕ) → Ordω n → Set
    OrdΩΩω : (n : ℕ) (α : Ordω n) → OrdΩω n α → Set
    OrdΛ : ℕ → Set
```

我们还没有研究它们的具体实现, 因为 $\texttt{Ord}_{\Omega_1}$ 的折叠就已经遇到了困难.

## 最初几层的折叠

回顾前文

- $\texttt{Ord}_1$ 到 $\texttt{Ord}_0$ 的折叠是平凡的
- $\texttt{Ord}_2$ 到 $\texttt{Ord}_1$ 的折叠是平凡的
- $\texttt{Ord}_3$ 到 $\texttt{Ord}_2$ 的折叠就是各种增长层级
- 再往后的折叠就是通常所说的 OCF

举最初几层折叠为例. 先写出 $\texttt{Ord}_2, \texttt{Ord}_3, \texttt{Ord}_4$ 的定义.

```agda
module NaiveCollapsing where
  open import Data.Nat renaming (ℕ to Ord₂)

  data Ord₃ : Set where
    zero : Ord₃
    suc : Ord₃ → Ord₃
    lim : (Ord₂ → Ord₃) → Ord₃

  data Ord₄ : Set where
    zero : Ord₄
    suc : Ord₄ → Ord₄
    lim : (Ord₂ → Ord₄) → Ord₄
    Lim : (Ord₃ → Ord₄) → Ord₄
```

$\texttt{Ord}_3$ 到 $\texttt{Ord}_2$ 的折叠的例子有 Hardy 层级

```agda
  hardy : Ord₃ → Ord₂ → Ord₂
  hardy zero n = n
  hardy (suc α) n = hardy α (suc n)
  hardy (lim f) n = hardy (f n) n
```

慢速增长层级

```agda
  slow : Ord₃ → Ord₂ → Ord₂
  slow zero n = 0
  slow (suc α) n = suc (slow α n)
  slow (lim f) n = slow (f zero) n
```

简单推广则有 $\texttt{Ord}_4$ 到 $\texttt{Ord}_3$ 的折叠

```agda
  Hardy : Ord₄ → Ord₃ → Ord₃
  Hardy zero α = α
  Hardy (suc μ) α = Hardy μ (suc α)
  Hardy (lim f) α = lim λ n → Hardy (f n) α
  Hardy (Lim F) α = Hardy (F α) α

  Slow : Ord₄ → Ord₂ → Ord₃
  Slow zero n = {!   !}
  Slow (suc μ) n = {!   !}
  Slow (lim f) n = {!   !}
  Slow (Lim Ord_Omega_fixpoint) n = {!   !}
```

## BO, TFBO, 及其上不远的位置

## 为什么 EBO 是困难的

“自下而上使用相同基本列”这个意义下的真前段
