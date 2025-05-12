# 为什么用树序数的方法折叠EBO是困难的

还是决定写篇文章详细解释一下现在的总体思路以及遇到的困难.

```agda
module OCF.Roadmap where
```

首先, 从零开始 (字面意义), 我们能看得跟清晰一些.

```agda
module Cf_literal where

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

实际上是共尾度的枚举

$$0, 1, \omega, \omega_1, \omega_2, ...$$

(可以认为0不是共尾度不过这无关紧要)

由此我们把它们重命名为 $\texttt{Cf}_\alpha$

$$
\begin{align}
\texttt{Cf}_0 &:= 0 \\
\texttt{Cf}_1 &:= 1 \\
\texttt{Cf}_2 &:= \omega \\
\texttt{Cf}_3 &:= \omega_1 \\
\texttt{Cf}_4 &:= \omega_2 \\
\end{align}
$$

当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

不难看出 $\texttt{Cf}_1$ 到 $\texttt{Cf}_0$ 以及 $\texttt{Cf}_2$ 到 $\texttt{Cf}_1$ 的折叠是平凡的.

而 $\texttt{Cf}_3$ 到 $\texttt{Cf}_2$ 的折叠就是各种增长层级.

再往后的折叠就是通常所说的 OCF. 只不过通常的定义是非直谓的, 从某个很大的 $\texttt{Cf}_\alpha$ 折叠到 $\texttt{Cf}_3$, 而我们这里需要明确的递归算法一层一层往下: $\texttt{Cf}_\alpha$ 到 ... 到 $\texttt{Cf}_4$ 到 $\texttt{Cf}_3$ (大可数序数) 到 $\texttt{Cf}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Cf}_\alpha$, 二是一层层折叠到 $\texttt{Cf}_2$.

只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一很多附加的要求导致很大的 $\texttt{Cf}_\alpha$ 也难以实现. 我们一步步看.

## 任务一

首先由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Cf}_{<\omega}$. 下标代表了构造子的个数.

归纳这个模式, 稍微借鉴一下类型宇宙的技巧我们可以写出 `Cf : ℕ → Set`.

```agda
module Cf_omega where
  -- 不难证明开篇代码定义的 `ℕ` 与标准库的 `ℕ` 同构, 方便起见直接从库中导入.
  open import Data.Nat hiding (_<_)

  -- 但是序采用以下定义
  data _<_ : ℕ → ℕ → Set where
    base : ∀ {n} → n < suc n
    step  : ∀ {n m} → n < m → n < suc m

  -- 假设所有 `k < n` 层已经定义完成, 定义第 `n` 层
  data U (n : ℕ) (E : ∀ k → k < n → Set) : Set where
    seq : (k : ℕ) (p : k < n) (a : E k p → U n E) → U n E

  -- 递归完成所有 `k < n` 层的定义
  Elm : ∀ n k → k < n → Set
  Elm (suc k) k base = U k (Elm k)
  Elm (suc n) k (step p) = Elm n k p

  -- 以自然数为下标的 `Cf` 层级
  Cf : ℕ → Set
  Cf n = U n (Elm n)
```

$\texttt{Cf}_4$ 到 $\texttt{Cf}_3$ 的折叠是已知可以实现的.

“自下而上使用相同基本列”这个意义下的真前段
