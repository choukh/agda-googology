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

本文可能是该系列的最后一篇, 因为遵循该纲领, 我们目前卡在了 $\psi(\Omega_\Omega)$. 为了引起关注, 我们将其命名为布劳威尔树壁垒序数 (Brouser Brw Barrier Ordinal), 简称 BTBO. 本文将介绍该序数的实现.

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
\mathbf{1}&:=\cfrac{\;\mathbf{0}\to\mathbf{1}\;}{\mathbf{1}}\;\text{zero}
\\[2em]
\mathbb{N}&:=\cfrac{\;\mathbf{0}\to\mathbb{N}\;}{\mathbb{N}}\;\text{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{N}\;}{\mathbb{N}}\;\text{suc}
\\[2em]
\mathbb{O}_0&:=\cfrac{\;\mathbf{0}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\text{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\text{suc}\;\;\;\;\cfrac{\;\mathbb{N}\to\mathbb{O}_0\;}{\mathbb{O}_0}\;\text{lim}
\\[2em]
\mathbb{O}_1&:=\cfrac{\;\mathbf{0}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\text{zero}\;\;\;\;\cfrac{\;\mathbf{1}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\text{suc}\;\;\;\;\cfrac{\;\mathbb{N}\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\text{lim}\;\;\;\;\cfrac{\;\mathbb{O}_0\to\mathbb{O}_1\;}{\mathbb{O}_1}\;\text{lim}_1
\end{align}
$$

```agda
module Brw_basic where

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
module Ord_basic where
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

`O₀`, `O₁` 的定义方便往上归纳定义 $\texttt{Brw}_\alpha$, 而 `Ord₀`, `Ord₁` 则方便直接使用.

为了方便表述, 我们把这些类型记作 $\texttt{Brw}_\alpha$ 或者 $\texttt{Ord}_\alpha$. 它们有如下关系

$$
\texttt{Ord}_\alpha :=
\begin{cases}
   \texttt{Brw}_{\alpha+3} &\text{if } \alpha < \omega \\
   \texttt{Brw}_\alpha &\text{if } \alpha\ge\omega
\end{cases}
$$

当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

将布劳威尔树 $\texttt{Brw}_\alpha$ 所能表示的序数的上确界记作 $\sup(\texttt{Brw}_\alpha)$, 并按 Buchholz 的惯例令

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
\sup(\texttt{Brw}_0) &= 0 \\
\sup(\texttt{Brw}_1) &= 1 \\
\sup(\texttt{Brw}_2) &= \omega \\
\sup(\texttt{Brw}_3) &= \Omega \\
\sup(\texttt{Brw}_4) &= \Omega_2 \\
...
\end{align}
$$

**约定** 如果一个类型 `A` 被当作序数, 我们指该类型所能表示的序数的上确界 $\sup(A)$.

考虑 $\texttt{Brw}_{\alpha^+}$ 到 $\texttt{Brw}_{\alpha}$ 的折叠. 从最底层开始, $\texttt{Brw}_1$ 到 $\texttt{Brw}_0$ 以及 $\texttt{Brw}_2$ 到 $\texttt{Brw}_1$ 的折叠是平凡的. 而 $\texttt{Brw}_3$ 到 $\texttt{Brw}_2$ 的折叠就是各种增长层级. 再往后的折叠就是通常所说的 OCF.

只不过通常的 OCF 使用集合论语言的非直谓定义, 而我们这里需要具体的递归算法一层一层往下: $\texttt{Brw}_\alpha$ 到 ... 到 $\texttt{Brw}_4$ 到 $\texttt{Brw}_3$ (大可数序数), 最后到 $\texttt{Brw}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Brw}_\alpha$, 二是一层层折叠到 $\texttt{Brw}_2$. 只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一附加很多要求. 我们一步步来.

## 自然数层布劳威尔树

我们需要等号 `_≡_` 及其性质.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

transport : {A B : Set} → A ≡ B → A → B
transport refl x = x
```

还需要自然数上的 $<$ 序及其传递性. 方便起见, 采用以下归纳定义.

**定义 ($<$)**  
$$
\cfrac{}{\;n<n^+\;}\;\;\text{zero}\;\;\;\;\;\;\;\cfrac{n<m}{\;n<m^+\;}\;\;\text{suc}
$$

```agda
module Nat_lt where
  variable n m o : ℕ

  data _<_ : ℕ → ℕ → Set where
    zero : n < suc n
    suc  : n < m → n < suc m
```

容易证明其传递性.

```agda
  <-trans : m < n → n < o → m < o
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
```

由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Brw}_{<\omega}$. 伪代码如下

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

归纳这个模式, 稍微使用一些类型宇宙的技巧我们可以定义 `Brw : ℕ → Set` 这个类型族.

```agda
module Brw_nat where
  open Nat_lt
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

这样我们就定义了任意 $\texttt{Brw}_n$. 虽然它只需要一个构造子“族”, 非常优雅, 但不方便使用. 从现在起我们改用 $\texttt{Ord}_n$ 层级, 显式写出最初的三个构造子 `zero`, `suc`, `lim`, 其后才使用族 `limₙ`.

```agda
module Ord_nat where
  open Nat_lt public
  private variable i : ℕ

  module _ (n : ℕ) (Ord< : ∀ i → i < n → Set) where
    data Ord₊ : Set where
      zero : Ord₊
      suc  : Ord₊ → Ord₊
      lim  : (f : ℕ → Ord₊) → Ord₊
      limₙ : (p : i < n) (f : Ord< i p → Ord₊) → Ord₊
```

剩下的定义跟 $\texttt{Brw}_n$ 是一样的. 给定 $n$, 我们递归定义满足 $p:i<n$ 的任意 $i$ 所给出的树 $\texttt{Ord}_{<i,\;p\,:\,i<n}$. 并定义

$$
\texttt{Ord}_n := \texttt{Ord}_{<n,\;\text{zero}\,:\,n<n^+}
$$

```agda
  Ord< : ∀ i → i < n → Set
  Ord< i zero = Ord₊ i Ord<
  Ord< i (suc p) = Ord< i p

  Ord : ℕ → Set
  Ord n = Ord< n zero
```

## $\omega2$ 层布劳威尔树

继续往上, 把 `Ord : ℕ → Set` 封装进构造子 `limₙ`, 它允许构造共尾度为任意 $\sup(\texttt{Ord}_n)$ 的序数, 这样就得到了 $\texttt{Brw}_\omega$.

```agda
  data Ordω : Set where
    zero : Ordω
    suc  : Ordω → Ordω
    lim  : (f : ℕ → Ordω) → Ordω
    limₙ : (n : ℕ) (f : Ord n → Ordω) → Ordω
```

再添加共尾度为 $\sup(\texttt{Ord}_\omega)$ 的序数, 就得到了 $\texttt{Ord}_{\omega+1}$.

```agda
  data Ordω+1 : Set where
    zero : Ordω+1
    suc  : Ordω+1 → Ordω+1
    lim  : (f : ℕ → Ordω+1) → Ordω+1
    limₙ : (n : ℕ) (f : Ord n → Ordω+1) → Ordω+1
    limω : (f : Ordω → Ordω+1) → Ordω+1
```

重复上述过程可以得到 $\texttt{Ord}_{\omega+n}$, $\texttt{Ord}_{\omega2}$ 和 $\texttt{Ord}_{\omega2+1}$.

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

前面说过, 一个布劳威尔树类型 `Ord n` 本身可以视作一个 $\Omega$ 数, 代表该类型的项所能表示的序数的上确界. 现在我们转而研究该类型的项所能表示的最大 $\Omega$ 数, 我们称为**内 $\Omega$ 数**, 记作 `Ω n : Ord n`. 首先我们需要定义一个嵌入操作.

**定义 (向上嵌入)** 对任意 $n : \mathbb{N}$, 递归定义 $\text{Ord}_n$ 到 $\text{Ord}_{n^+}$ 的嵌入 $↑_+$ 如下:

- 如果 $a : \text{Ord}_n$ 由 `zero`, `suc` 或 `lim` 构造, 我们直接使用 $\text{Ord}_{n^+}$ 的同名构造子递归构造 $↑_+a$.
- 如果 $a = \text{lim}_n(p,f)$, 其中 $p:i<n$ 且 $f:\texttt{Ord}_{<i,\;p}\to\text{Ord}_n$, 则 $↑_+a:=\text{lim}_n(\text{suc}(p),↑_+\circ f)$, 其中 $\text{suc}(p):i<n^+$ 且 $↑_+\circ f:\texttt{Ord}_{<i,\;p}\to\text{Ord}_{n^+}$.

```agda
  ↑₊ : Ord n → Ord (suc n)
  ↑₊ zero = zero
  ↑₊ (suc a) = suc (↑₊ a)
  ↑₊ (lim f) = lim (↑₊ ∘ f)
  ↑₊ (limₙ p f) = limₙ (suc p) (↑₊ ∘ f)
```

向上嵌入允许我们在 $\text{Ord}_{n^+}$ 中表达 $↑:\text{Ord}_{n}\to\text{Ord}_{n^+}$ 的极限, 该极限就是我们所需的内 $\Omega$ 数.

**定义 (Ω数)** 遵循 [Buchholz](https://en.wikipedia.org/wiki/Buchholz_psi_functions) 的定义

$$
\Omega_n :=
\begin{cases}
   1 &\text{if } n = 0 \\
   \omega_n &\text{if } n > 0
\end{cases}
$$

```agda
  Ω : (n : ℕ) → Ord n
  Ω zero    = suc zero
  Ω (suc n) = limₙ zero ↑₊
```

```agda
  ↑ω : Ord n → Ordω
  ↑ω zero = zero
  ↑ω (suc a) = suc (↑ω a)
  ↑ω (lim f) = lim (↑ω ∘ f)
  ↑ω (limₙ p f) = limₙ _ (λ x → ↑ω (f {! x  !}))
```

```agda
  Ωω : Ordω
  Ωω = lim (λ n → limₙ n ↑ω)
```

将目前的成果总结如下:

|类型|上确界|内$\Omega$数|内$\Omega$数共尾度|
|-|-|-|-|
|$\mathbb{0}$|$0$|n/a|n/a|
|$\mathbb{1}$|$1$|$0$|$0$|
|$\mathbb{N}$|$\omega$|$1$|$1$|
|$\texttt{Ord}_0$|$\Omega$|$\omega$|$\omega$|
|$\texttt{Ord}_1$|$\Omega_2$|$\Omega$|$\Omega$|
|$\texttt{Ord}_2$|$\Omega_3$|$\Omega_2$|$\Omega_2$|
|$\texttt{Ord}_n$|$\Omega_{n+1}$|$\Omega_n$|$\Omega_n$|
|$\texttt{Ord}_{\omega}$|$\Omega_{\omega+1}$|$\Omega_\omega$|$\omega$|
|$\texttt{Ord}_{\omega+1}$|$\Omega_{\omega+2}$|$\Omega_{\omega+1}$|$\Omega_{\omega+1}$|
|$\texttt{Ord}_{\omega+n}$|$\Omega_{\omega+n+1}$|$\Omega_{\omega+n}$|$\Omega_{\omega+n}$|
|$\texttt{Ord}_{\omega2}$|$\Omega_{\omega2+1}$|$\Omega_{\omega2}$|$\omega$|
|$\texttt{Ord}_{\omega2+1}$|$\Omega_{\omega2+2}$|$\Omega_{\omega2+1}$|$\Omega_{\omega2+1}$|

为了一劳永逸地定义 $\texttt{Ord}_\alpha$, 其中 $\alpha < \Omega$, 我们要以可数序数 $\texttt{Ord}_0$ 为下标, 写出一个新的类型族 `Ord : Ord₀ → Set`.

## 可数序数的有界三歧性

引入和类型, 并定义构造子模式简写.

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)
```

```agda
module Nat where
  open Nat_lt hiding (<-trans) public

  z<s : ∀ n → zero < suc n
  z<s zero    = zero
  z<s (suc n) = suc (z<s n)

  s<s : n < m → suc n < suc m
  s<s zero      = zero
  s<s (suc p)  = suc (s<s p)

  <-dec : ∀ n m → n < m ⊎ m < n ⊎ n ≡ m
  <-dec zero zero = injᶜ refl
  <-dec zero (suc m) = injᵃ (z<s m)
  <-dec (suc n) zero = injᵇ (z<s n)
  <-dec (suc n) (suc m) with <-dec n m
  ... | injᵃ p = injᵃ (s<s p)
  ... | injᵇ p = injᵇ (s<s p)
  ... | injᶜ p = injᶜ (cong suc p)

module Ordᴰ where
  open Nat renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)

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

  f<l : ∀ n → f n < lim f mono
  f<l {mono} n = lim (suc n) (mono zero)

  <-trans : a < b → b < c → a < c
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
  <-trans p (lim n q) = lim n (<-trans p q)

  <-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b
  <-dec zero zero       = injᶜ refl
  <-dec zero (suc q)    = injᵇ q
  <-dec (suc p) zero    = injᵃ p
  <-dec (suc p) (suc q) = <-dec p q
  <-dec (lim {mono} n p) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m  = <-dec (<-trans p (mono n<m)) q
  ... | injᵇ m<n  = <-dec p (<-trans q (mono m<n))
  ... | injᶜ refl = <-dec p q

  mutual
    _+_ : Ordᴰ → Ordᴰ → Ordᴰ
    a + zero          = a
    a + suc b         = suc (a + b)
    a + lim f f-mono  = lim (λ n → a + f n) (+-mono ∘ f-mono)

    +-mono : b < c → a + b < a + c
    +-mono zero       = zero
    +-mono (suc p)    = suc (+-mono p)
    +-mono (lim n p)  = lim n (+-mono p)

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

  a<a+b : ⦃ _ : NonZero b ⦄ → a < a + b
  a<a+b = +-mono (z<nz it)

  -- cumulative sum
  cumsum : (ℕ → Ordᴰ) → (ℕ → Ordᴰ)
  cumsum f zero     = f zero
  cumsum f (suc n)  = cumsum f n + suc (f (suc n))

  cumsum-mono : (f : ℕ → Ordᴰ) → monotonic (cumsum f)
  cumsum-mono f zero    = a<a+b
  cumsum-mono f (suc p) = <-trans (cumsum-mono f p) a<a+b
```

## 可数序数层布劳威尔树

```agda
module Ord_ord where
  open Ordᴰ hiding (_+_)
  private variable i ℓ ℓ₁ ℓ₂ : Ordᴰ

  module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
    data Ord₊ : Set where
      zero  : Ord₊
      suc   : Ord₊ → Ord₊
      lim   : (f : ℕ → Ord₊) → Ord₊
      limₗ  : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊

  Ord< : (i : Ordᴰ) (p : i < ℓ) → Set
  Ord< i zero      = Ord₊ i Ord<
  Ord< i (suc p)   = Ord< i p
  Ord< i (lim n p) = Ord< i p

  Ord : Ordᴰ → Set
  Ord ℓ = Ord< ℓ zero

  Ord₀ : Set
  Ord₀ = Ord zero

  Ord<-≡ : (p : i < ℓ₁) (q : i < ℓ₂) → Ord< i p ≡ Ord< i q
  Ord<-≡ zero zero      = refl
  Ord<-≡ (suc p) zero   = Ord<-≡ p zero
  Ord<-≡ (lim n p) zero = Ord<-≡ p zero
  Ord<-≡ p (suc q)      = trans (Ord<-≡ p q) refl
  Ord<-≡ p (lim n q)    = trans (Ord<-≡ p q) refl

  coe : {p : i < ℓ₁} {q : i < ℓ₂} → Ord< i p → Ord< i q
  coe {p} {q} = transport (Ord<-≡ p q)

  coe₀ : {p : i < ℓ₂} → Ord i → Ord< i p
  coe₀ = coe {p = zero}

  ↑ : ℓ₁ < ℓ₂ → Ord ℓ₁ → Ord ℓ₂
  ↑ p zero        = zero
  ↑ p (suc a)     = suc (↑ p a)
  ↑ p (lim f)     = lim (↑ p ∘ f)
  ↑ p (limₗ q f)  = limₗ (<-trans q p) (↑ p ∘ f ∘ coe)

  Ω : (ℓ : Ordᴰ) → Ord ℓ
  Ω zero          = suc zero
  Ω (suc ℓ)       = limₗ zero (↑ zero)
  Ω (lim f mono)  = lim (λ n → ↑ (f<l n) (Ω (f n)))
  ```

## 布劳威尔树的折叠

  ```agda
  _+_ : Ord ℓ → Ord ℓ → Ord ℓ
  a + zero = a
  a + suc b = suc (a + b)
  a + lim f = lim (λ n → a + f n)
  a + limₗ p f = limₗ p (λ x → a + f x)

  iter : {T : Set} (f : T → T) (init : T) (times : ℕ) → T
  iter f a zero    = a
  iter f a (suc n) = f (iter f a n)

  lfp : (Ord ℓ → Ord ℓ) → Ord ℓ
  lfp f = lim (iter f zero)

  -- Buchholz's ψ
  ψ< : i < ℓ → Ord ℓ → Ord i
  ψ< p zero     = Ω _
  ψ< p (suc a)  = lfp (ψ< p a +_)
  ψ< p (lim f)  = lim (ψ< p ∘ f)
  ψ< {i} {ℓ} p (limₗ {i = j} q f) with <-dec q p
  ... | injᵃ j<i  = limₗ j<i (ψ< p ∘ f ∘ coe)
  ... | injᵇ i<j  = lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)
  ... | injᶜ refl = lfp (ψ< p ∘ f ∘ coe₀)

  ψ₀ : Ord ℓ → Ord₀
  ψ₀ {ℓ = zero}       a = a
  ψ₀ {ℓ = suc ℓ}      a = ψ₀ (ψ< zero a)
  ψ₀ {ℓ = lim f mono} a = lim (λ n → ψ₀ (ψ< (f<l n) a))

  ordᴰ : Ord₀ → Ordᴰ
  ordᴰ zero     = zero
  ordᴰ (suc a)  = suc (ordᴰ a)
  ordᴰ (lim f)  = lim (cumsum (ordᴰ ∘ f)) (cumsum-mono (ordᴰ ∘ f))

  -- n-iteration of ψ₀(Ω_x)
  ψⁿ : ℕ → Ord₀
  ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero

  ex1 = ψⁿ 1    -- ω
  ex2 = ψⁿ 2    -- Buchholz's ordinal
  ex3 = ψⁿ 3    -- ψ(Ω_BO)
  ex4 = ψⁿ 4    -- ψ(Ω_ψ(Ω_BO))

  -- Brouwer tree barrier ordinal
  BTBO : Ord₀
  BTBO = lim ψⁿ -- ψ(Ω_Ω)

  FGH : Ord₀ → ℕ → ℕ
  FGH zero    n = suc n
  FGH (suc a) n = iter (FGH a) n n
  FGH (lim a) n = FGH (a n) n

  mynum : ℕ
  mynum = FGH BTBO 99
```

## 参考

- [Andras Kovacs - Large countable ordinals and numbers in Agda](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a?permalink_comment_id=5617267)
- [ccz181078 - googology](https://github.com/ccz181078/googology)
- [Thierry Coquand - Inductive Definitions and Constructive Mathematics](https://www.cse.chalmers.se/~coquand/prague1.pdf)
- [Googology Wiki - Ordinal collapsing function](https://googology.fandom.com/wiki/Ordinal_collapsing_function)
- [ユーザーブログ:Hexirp - ブラウワー順序数の制限と拡張](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/ブラウワー順序数の制限と拡張)
- [ユーザーブログ:Hexirp - 2024-12-25 のメモ](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/2024-12-25_のメモ)

## 附录

[ccz181078](https://github.com/ccz181078) 使用[另一种类似的方法](https://github.com/ccz181078/googology/blob/main/BuchholzOCF.v) 实现了 $\texttt{Ord}_n$, 但似乎更难以往上推广. 我们给出该方法的 Agda 版本, 以供参考.

```agda
module Ord_nat_ccz181078 where
  open Ord_basic

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
