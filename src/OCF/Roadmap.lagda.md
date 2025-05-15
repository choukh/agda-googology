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
open import Data.Nat using (ℕ; suc; zero)
```

## 什么是树序数

首先, 从零开始 (字面意义), 我们能看得更清晰一些.

```agda
module Tree_literal where

  data 𝟎 : Set where

  data 𝟏 : Set where
    zero : (𝟎 → 𝟏) → 𝟏

  data 𝕆₀ : Set where
    zero : (𝟎 → 𝕆₀) → 𝕆₀
    suc : (𝟏 → 𝕆₀) → 𝕆₀

  data 𝕆₁ : Set where
    zero : (𝟎 → 𝕆₁) → 𝕆₁
    suc : (𝟏 → 𝕆₁) → 𝕆₁
    lim : (𝕆₀ → 𝕆₁) → 𝕆₁

  data 𝕆₂ : Set where
    zero : (𝟎 → 𝕆₂) → 𝕆₂
    suc : (𝟏 → 𝕆₂) → 𝕆₂
    lim : (𝕆₀ → 𝕆₂) → 𝕆₂
    lim₁ : (𝕆₁ → 𝕆₂) → 𝕆₂
```

这样的一系列类型的项所能表示的序数就叫做树序数 (tree ordinal), 又叫布劳威尔序数 (Brouwer ordinal). 为了方便表述, 非形式地, 我们把这里的 `𝟎`, `𝟏`, `𝕆₀`, `𝕆₁`, `𝕆₂`, ... 记作 $\texttt{Tree}_\alpha$. 当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

不难看出

- `𝟎` 与标准库的 `⊥` 同构
- `𝟏` 与标准库的 `⊤` 同构
- `𝕆₀` 与标准库的 `ℕ` 同构

而 `𝕆₁` 和 `𝕆₂` 又与如下定义的 `Ord`, `Ord₂` 同构

```agda
data Ord : Set where
  zero : Ord
  suc : Ord → Ord
  lim : (ℕ → Ord) → Ord

data Ord₂ : Set where
  zero : Ord₂
  suc : Ord₂ → Ord₂
  lim : (ℕ → Ord₂) → Ord₂
  lim₁ : (Ord → Ord₂) → Ord₂
```

`𝕆₁`, `𝕆₂` 的定义方便往上归纳定义 $\texttt{Tree}_\alpha$, 而 `Ord`, `Ord₂` 则方便直接使用.

我们认为 $\texttt{Tree}_\alpha$ 所能表示的序数的上确界 (记作 $\sup$) 分别为

$$0, 1, \omega, \omega_1, \omega_2, ...$$

即有

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

不难看出 $\texttt{Tree}_1$ 到 $\texttt{Tree}_0$ 以及 $\texttt{Tree}_2$ 到 $\texttt{Tree}_1$ 的折叠是平凡的.

而 $\texttt{Tree}_3$ 到 $\texttt{Tree}_2$ 的折叠就是各种增长层级.

再往后的折叠就是通常所说的 OCF. 只不过通常的定义是非直谓的, 通过一个抽象的定义从某个很大的 $\texttt{Tree}_\alpha$ 一步折叠到 $\texttt{Tree}_3$, 而我们这里需要具体的递归算法一层一层往下: $\texttt{Tree}_\alpha$ 到 ... 到 $\texttt{Tree}_4$ 到 $\texttt{Tree}_3$ (大可数序数) 到 $\texttt{Tree}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Tree}_\alpha$, 二是一层层折叠到 $\texttt{Tree}_2$.

只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一很多附加的要求, 导致很大的 $\texttt{Tree}_\alpha$ 也难以实现. 我们一步步看.

## 任务一: $\Omega_{\Omega_{._{._.}}}$的实现路径

首先由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Tree}_{<\omega}$. 伪代码如下

```pseudocode
data Treeₖ₊₁ : Set where
  cf₀ : (Tree₀ → Treeₖ₊₁) → Treeₖ₊₁
  cf₁ : (Tree₁ → Treeₖ₊₁) → Treeₖ₊₁
  ...
  cfₖ : (Treeₖ → Treeₖ₊₁) → Treeₖ₊₁
```

其中下标 `k + 1` 代表了不同构造子的个数, 而下标为 `k` 的构造子则构造了以 `Treeₖ` 为长度的基本列.

- `cf₀` 构造了长度为 $\texttt{Tree}_0 = 0$ 的基本列, 它只有一个, 就是空列 `λ ()`, 代表序数 $0$
- `cf₁` 构造了长度为 $\texttt{Tree}_1 = 1$ 的基本列, 代表了该基本列的唯一元素的后继.
- `cf₂` 构造了长度为 $\texttt{Tree}_2 = \omega$ 的基本列, 代表基本列的极限.
- `cf₃` 构造了长度为 $\texttt{Tree}_3 = \omega_1$ 的基本列, 代表更高阶的极限.
- ...

归纳这个模式, 稍微使用一些类型宇宙的技巧我们可以写出 `Treeω : ℕ → Set` 这个类型族.

```agda
module Tree_omega where
  -- 方便起见, `ℕ` 的序采用以下定义
  data _<_ : ℕ → ℕ → Set where
    base : ∀ {n} → n < suc n
    step  : ∀ {n m} → n < m → n < suc m

  -- 假设下标为 `k < n` 的树序数 `E k` 已经定义完成, 定义下标为 `n` 的树序数 `U`
  module _ (n : ℕ) (E : ∀ k → k < n → Set) where
    data U : Set where
      -- `U` 的元素的共尾度 (基本列的长度) 为任意满足 `k < n` 的 `E k`
      cf : (k : ℕ) (p : k < n) (f : E k p → U) → U

  -- 递归完成所有 `k < n` 的树序数的定义
  E : ∀ {n} k → k < n → Set
  E k base = U k E
  E k (step p) = E k p

  -- 消掉 `k < n` 的条件
  Treeω : ℕ → Set
  Treeω n = E n base
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

总之, 我们以 `ℕ` 为下标, 写出了 `Treeω`, 它形式化了 $\texttt{Ord}_{\omega}$, 满足

$$
\sup(\texttt{Ord}_\omega) = \Omega_\omega
$$

[ccz181078](https://github.com/ccz181078) 使用[另一种方法](https://github.com/ccz181078/googology/blob/main/BuchholzOCF.v)实现了 $\texttt{Ord}_\omega$, 但似乎更难以往上扩展. 我们给出该方法的 Agda 版本, 以供参考.

```agda
module Ord_omega where
  open import Data.Unit
  open import Data.Nat

  -- 假设某 `X = Ordₙ` 已完成, 并且已知任意 `x : X` 的共尾度 (基本列的长度) `cf x`
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

  -- 互递归完成下标为自然数的整个 `Ordₙ` 的层级以及每层的共尾度
  mutual
    Ordω : ℕ → Set
    Ordω zero = Ord
    Ordω (suc n) = Ord₊ (cfω n)

    cfω : (n : ℕ) → Ordω n → Set
    cfω zero _ = ⊤
    cfω (suc n) = cf₊ (cfω n)
```

接着 $\texttt{Tree}_\omega$ 的定义继续往上, 规律很明显了. 我们要以 $\texttt{Ord}$ 为下标, 写出一个新的类型族 `OrdΩ : Ord → Set`. 具体方法参考 Andras Kovacs 的 [Gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 中的 `U`. 它形式化了 $\texttt{Ord}_\Omega$, 上确界为 $\Omega_{\Omega}$. Andras Kovacs 用它写出了 $\psi(\Omega_{\varepsilon_0}) = \text{PTO}(\text{ID}_{<\varepsilon_0})$, 其中 $\psi$ 是 [Madore 的 $\psi$](https://googology.fandom.com/wiki/Madore%27s_function), 但扩张到了 $\Omega$ 多个 $\Omega$.

以此类推, 我们有

|类型族|索引类型|共尾度|上确界|
|-|-|-|-|
|$\texttt{Ord}_\omega$|$\N$|$\omega$|$\Omega_{\omega}$|
|$\texttt{Ord}_\Omega$|$\texttt{Ord}$|$\omega_1$|$\Omega_{\Omega}$|
|$\texttt{Ord}_{\Omega_2}$|$\texttt{Ord}_2$|$\omega_2$|$\Omega_{\Omega_2}$|
|...|...|...|...|
|$\texttt{Ord}_{\Omega_\omega}$|$\N,\texttt{Ord}_\omega$|$\omega$|$\Omega_{\Omega_\omega}$|
|$\texttt{Ord}_{\Omega_{\Omega_\omega}}$|$\N,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega}$|$\omega$|$\Omega_{\Omega_\omega}$|
|...|...|...|...|
|$\texttt{Ord}_{\Lambda}$|$\N,\texttt{Ord}_\omega,\texttt{Ord}_{\Omega_\omega},...$|$\omega$|$\Omega_{\Omega_{._{._.}}}$|

其中索引类型如果包含多个, 那么表示它是一个嵌套的依赖类型. 如果需要实现任意多层的嵌套, 可以先从 `ℕ` 递归得到类型签名, 所以签名可以简化到只剩 `ℕ` 索引. 从而最后三行可能将具有以下类型

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

先准备一些辅助函数

```agda
iter : {T : Set} → (T → T) → ℕ → T → T
iter f zero    m = m
iter f (suc n) m = f (iter f n m)
```

### $\Omega_2$的折叠

```agda
ψ : Ord₂ → Ord
ψ zero = suc zero
ψ (suc α) = suc (ψ α)
ψ (lim f) = lim (λ n → ψ (f n))
ψ (lim₁ f) = lim (λ x → {!   !})
```

```agda
module Tree_omega_collapsing where
  open Tree_omega
  open import Relation.Binary.PropositionalEquality

  U≡E : {k n : ℕ} (p : k < n) → U k E ≡ E k p
  U≡E base = refl
  U≡E (step p) = U≡E p

  coe : {A B : Set} → A ≡ B → A → B
  coe refl x = x

  z<s : {n : ℕ} → 0 < suc n
  z<s {(zero)} = base
  z<s {suc n} = step z<s

  zeroᵀ : {n : ℕ} → Treeω (suc n)
  zeroᵀ = cf 0 z<s λ { x → {! x  !} }

  FGH : Treeω 3 → Treeω 2 → Treeω 2
  FGH (cf 2 base f) n = FGH (f n) n
  FGH (cf 1 (step base) α) n = iter (FGH (α zeroᵀ)) {! n  !} n
  FGH (cf 0 (step (step base)) _) n = cf 1 base λ _ → n
  FGH (cf _ (step (step (step ()))) _) _
```

### $\Omega_{\omega}$ 乃至 $\Omega_{\Omega}$ 的折叠

### 为什么 $\Omega_{\Omega_2}$ 的折叠是困难的

“自下而上使用相同基本列”这个意义下的真前段

## 参考

- [Andras Kovacs - Large countable ordinals and numbers in Agda](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a)
- [ccz181078 - googology](https://github.com/ccz181078/googology)
- [Thierry Coquand - Inductive Definitions and Constructive Mathematics](https://www.cse.chalmers.se/~coquand/prague1.pdf)
- [Googology Wiki - Ordinal collapsing function](https://googology.fandom.com/wiki/Ordinal_collapsing_function)
- [ユーザーブログ:Hexirp - ブラウワー順序数の制限と拡張](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/ブラウワー順序数の制限と拡張)
- [ユーザーブログ:Hexirp - 2024-12-25 のメモ](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/2024-12-25_のメモ)
