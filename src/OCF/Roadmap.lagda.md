# 为什么用树序数的方法折叠EBO是困难的

还是决定写篇文章详细解释一下现在的总体思路以及遇到的困难.

```agda
module OCF.Roadmap where
```

首先, 从零开始 (字面意义), 我们能看得跟清晰一些.

```agda
module OrdLiteral where

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

## 任务一

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

归纳这个模式, 稍微借鉴一下类型宇宙的技巧我们可以写出 `Ord : ℕ → Set`.

```agda
module Ordω where
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

  -- 完成以自然数为下标的 `Ord` 层级
  Ord : ℕ → Set
  Ord n = U n (Elm n)
```

下面将这个 `Ord : ℕ → Set` 简记作 `Ordω`, 并引入传统记法 $\Omega$. 虽然 $\Omega$ 跟 `Ordω` 的下标没有完全对齐, 但我们可以说此时能达到的大致“量级”是 $\Omega_n$, 上确界为 $\Omega_{\omega}$. 在这层意义上我们可以说 `Ordω` 等于 $\Omega_{\omega}$.

继续往上, 很明显了, 我们要以 $\texttt{Ord}_3$ 为下标, 写出一个新的 `Ord` 层级, 那么就可以达到 $\Omega_\omega$, 上确界为 $\Omega_{\Omega}$.

```agda
-- TODO
```

以此类推, 我们有

|下标类型|上确界|可达量级|
|-|-|-|
|$\texttt{Ord}_2$|$\Omega_{ \omega}$|$\Omega_n$|
|$\texttt{Ord}_3$|$\Omega_{ \Omega}$|$\Omega_{\omega}$|
|$\texttt{Ord}_4$|$\Omega_{\Omega_1}$|$\Omega_{\Omega}$|
|$\texttt{Ord}_5$|$\Omega_{\Omega_2}$|$\Omega_{\Omega_1}$|
|...|...|...|...|...|
|$\texttt{Ord}_\omega$|$\Omega_{ \Omega_\omega}$|$\Omega_{\Omega_n}$|

`Ord_ω : (n : Ord 2) → Ord n → Set`

`Ord_Ω : (α : Ord 3) → Ord α → Set`

`Ord_I : (n : Ord 2) (α : Ord n) → Ord α → Set`

## 任务二

$\texttt{Ord}_4$ 到 $\texttt{Ord}_3$ 的折叠是已知可以实现的.

“自下而上使用相同基本列”这个意义下的真前段
