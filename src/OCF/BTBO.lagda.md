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

本文可能是该系列的最后一篇, 因为遵循该纲领, 我们目前卡在了 $\psi(\Omega_\Omega)$, 其中 $\psi$ 是 [Madore 的 $\psi$](https://googology.fandom.com/wiki/Madore%27s_function). 为了引起重视, 我们将其命名为布劳威尔树壁垒序数 (Brouser Brw Barrier Ordinal), 简称 BTBO. 本文将介绍该序数的实现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.BTBO where
```

## 布劳威尔树

什么是布劳威尔树? 从零开始 (字面意义), 我们能看得更清晰一些.

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

这样的一系列类型就叫布劳威尔树, 它们的项所能表示的序数就叫布劳威尔树序数. 为了方便表述, 非形式地, 我们把这些类型记作 $\texttt{Brw}_\alpha$. 当然这里的下标 $\alpha$ 的类型目前是非形式地, 根据上下文它可能是自然数, 可能是某个小于 $\omega_\beta$ 的数, 而这里的 $\beta$ 也跟 $\alpha$ 一样类型未定. 为了讨论我们总得先往前说.

有时候为了对齐某些下标, 我们也会使用 $\texttt{Ord}$ 的记法

$$
\begin{align}
\texttt{Ord}_n &:= \texttt{Brw}_{n+3}\;\;\;&n<\omega \\

\texttt{Ord}_\alpha &:= \texttt{Brw}_\alpha\;\;\;&\alpha\ge\omega\\
\end{align}
$$

不难看出

- `𝟎` 与标准库的 `⊥` 同构
- `𝟏` 与标准库的 `⊤` 同构
- `ℕ` 与标准库的 `ℕ` 同构

而 `O₀` 和 `O₁` 又与如下定义的 `Ord₀`, `Ord₁` 同构

```agda
module Ord_basic where
  open import Data.Nat using (ℕ)

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

将布劳威尔树 $\texttt{Brw}_\alpha$ 所能表示的序数的上确界记作 $\sup(\texttt{Brw}_\alpha)$, 并按惯例令 $\Omega_\alpha := \omega_\alpha$, 其中 $\Omega_1$ 简记作 $\Omega$. 则有

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

考虑 $\texttt{Brw}_{\alpha^+}$ 到 $\texttt{Brw}_{\alpha}$ 的折叠. 从最底层开始,  $\texttt{Brw}_1$ 到 $\texttt{Brw}_0$ 以及 $\texttt{Brw}_2$ 到 $\texttt{Brw}_1$ 的折叠是平凡的. 而 $\texttt{Brw}_3$ 到 $\texttt{Brw}_2$ 的折叠就是各种增长层级. 再往后的折叠就是通常所说的 OCF.

只不过通常的 OCF 是非直谓的, 它通过一个抽象的描述从某个很大的 $\texttt{Brw}_\alpha$ 一步折叠到 $\texttt{Brw}_3$, 而我们这里需要具体的递归算法一层一层往下: $\texttt{Brw}_\alpha$ 到 ... 到 $\texttt{Brw}_4$ 到 $\texttt{Brw}_3$ (大可数序数) 到 $\texttt{Brw}_2$ (大自然数).

因此我们的任务主要分解成两部分, 一是写出很大的 $\texttt{Brw}_\alpha$, 二是一层层折叠到 $\texttt{Brw}_2$. 只考虑任务一的话是相对简单的, 难点在于我们后面会看到任务二会给任务一很多附加的要求. 我们一步步来.

## 大布劳威尔树的实现

首先由开篇的代码, 通过简单的复制粘贴我们可以写出任意 $\texttt{Brw}_{<\omega}$. 伪代码如下

```pseudocode
data Brwₖ₊₁ : Set where
  cf₀ : (Brw₀ → Brwₖ₊₁) → Brwₖ₊₁
  cf₁ : (Brw₁ → Brwₖ₊₁) → Brwₖ₊₁
  ...
  cfₖ : (Brwₖ → Brwₖ₊₁) → Brwₖ₊₁
```

其中 `Brwₖ₊₁` 的下标 `k + 1` 代表了该类型的构造子的个数, 而下标为 `k` 的构造子 `cfₖ` 则构造了共尾度至多为 $\sup(\texttt{Brw}_k)$ 的序数, 即这些序数的基本列的长度至多为 $\sup(\texttt{Brw}_k)$.

- `cf₀` 构造了长度为 $0$ 的基本列所能表示的序数, 它只有一个, 就是空列 `λ ()`, 代表序数 $0$
- `cf₁` 构造了长度为 $1$ 的基本列所能表示的序数, 代表了该基本列的唯一元素的后继.
- `cf₂` 构造了长度为 $\omega$ 的基本列所能表示的序数, 代表序数基本列的极限.
- `cf₃` 构造了长度为 $\Omega$ 的基本列所能表示的序数, 代表更高阶的极限.
- ...

归纳这个模式, 稍微使用一些类型宇宙的技巧我们可以写出 `Brw : ℕ → Set` 这个类型族.

```agda
module Brw_nat where
  open import Data.Nat using (ℕ; zero; suc )

  -- 方便起见, `ℕ` 的序采用以下定义
  data _<_ : ℕ → ℕ → Set where
    zero : ∀ {n} → n < suc n
    suc  : ∀ {n m} → n < m → n < suc m

  -- 假设下标为 `k < n` 的任意树 `Brw< k` 已经定义完成, 定义下标为 `n` 的树 `Brw₊`
  module _ (n : ℕ) (Brw< : ∀ k → k < n → Set) where
    data Brw₊ : Set where
      -- `Brw₊` 的元素的共尾度为任意满足 `k < n` 的 `Brw< k`
      cf : (k : ℕ) (p : k < n) (f : Brw< k p → Brw₊) → Brw₊

  -- 递归完成所有 `k < n` 的树序数的定义
  Brw< : ∀ {n} k → k < n → Set
  Brw< k zero = Brw₊ k Brw<
  Brw< k (suc p) = Brw< k p

  -- 消掉 `k < n` 的条件
  Brw : ℕ → Set
  Brw n = Brw< n zero
```

这样我们就形式化了任意 $\texttt{Brw}_n$. [ccz181078](https://github.com/ccz181078) 使用[另一种方法](https://github.com/ccz181078/googology/blob/main/BuchholzOCF.v)实现了 $\texttt{Ord}_n$, 但似乎更难以往上扩展. 我们给出该方法的 Agda 版本, 以供参考.

```agda
module Ord_nat where
  open import Data.Unit
  open import Data.Nat
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

有了 $\texttt{Brw}_n$ 的定义, 我们可以立即写出 $\texttt{Brw}_\omega$ 的定义.

接着 $\texttt{Brw}_\omega$ 的定义继续往上, 规律很明显了. 我们要以 $\texttt{Ord}$ 为下标, 写出一个新的类型族 `OrdΩ : Ord → Set`. 具体方法参考 Andras Kovacs 的 [Gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 中的 `U`. 它形式化了 $\texttt{Ord}_\Omega$, 上确界为 $\Omega_{\Omega}$. Andras Kovacs 用它写出了 $\psi(\Omega_{\varepsilon_0}) = \text{PTO}(\text{ID}_{<\varepsilon_0})$, 其中 $\psi$ 是 [Madore 的 $\psi$](https://googology.fandom.com/wiki/Madore%27s_function), 但扩张到了 $\Omega$ 多个 $\Omega$.

我们有如下对应关系:

|类型|共尾度|典型项|上确界|
|-|-|-|-|
|$\mathbb{0}$|n/a|n/a|$0$|
|$\mathbb{1}$|$0$|$0$|$1$|
|$\N$|$1$|$1$|$\omega$|
|$\texttt{Ord}_0$|$\omega$|$\omega$|$\Omega$|
|$\texttt{Ord}_1$|$\Omega$|$\Omega$|$\Omega_2$|
|$\texttt{Ord}_2$|$\Omega_2$|$\Omega_2$|$\Omega_3$|
|$\texttt{Ord}_n$|$\Omega_n$|$\Omega_n$|$\Omega_{n+1}$|
|$\texttt{Ord}_{\omega}$|$\omega$|$\Omega_\omega$|$\Omega_{\omega+1}$|
|$\texttt{Ord}_{\omega+1}$|$\Omega_{\omega+1}$|$\Omega_{\omega+1}$|$\Omega_{\omega+2}$|
|$\texttt{Ord}_{\omega+2}$|$\Omega_{\omega+2}$|$\Omega_{\omega+2}$|$\Omega_{\omega+3}$|
|...|...|...|...|

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

我们还没有研究它们的具体实现, 因为 $\texttt{Ord}_{\Omega_2}$ 的折叠就已经遇到了困难.

```agda
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; it)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)

transport : {A B : Set} → A ≡ B → A → B
transport refl x = x

module ℕ where
  open import Data.Nat using (ℕ; zero; suc) public
  variable n m : ℕ

  iter : {T : Set} (f : T → T) (init : T) (times : ℕ) → T
  iter f a zero    = a
  iter f a (suc n) = f (iter f a n)

  data _<_ : ℕ → ℕ → Set where
    zero : n < suc n
    suc  : n < m → n < suc m

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

open ℕ using (ℕ; zero; suc)

module Ordᴰ where
  infix 10 _<_
  data Ordᴰ : Set
  data _<_ : Ordᴰ → Ordᴰ → Set

  monotonic : (ℕ → Ordᴰ) → Set
  monotonic f = ∀ {n m} → n ℕ.< m → f n < f m

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
  <-dec (lim {mono} n p) (lim m q) with ℕ.<-dec n m
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

↑₀ : ℕ → Ord₀
↑₀ zero = zero
↑₀ (suc n) = suc (↑₀ n)

↑ : ℓ₁ < ℓ₂ → Ord ℓ₁ → Ord ℓ₂
↑ p zero        = zero
↑ p (suc a)     = suc (↑ p a)
↑ p (lim f)     = lim (↑ p ∘ f)
↑ p (limₗ q f)  = limₗ (<-trans q p) (↑ p ∘ f ∘ coe)

Ω : (ℓ : Ordᴰ) → Ord ℓ
Ω zero          = lim ↑₀
Ω (suc ℓ)       = limₗ zero (↑ zero)
Ω (lim f mono)  = lim (λ n → ↑ (f<l n) (Ω (f n)))

iter : (f : Ord ℓ → Ord ℓ) (init : Ord ℓ) (times : Ord ℓ) → Ord ℓ
iter f a zero       = a
iter f a (suc b)    = f (iter f a b)
iter f a (lim g)    = lim (iter f a ∘ g)
iter f a (limₗ p g) = limₗ p (iter f a ∘ g)

_+_ _*_ _^_ : Ord ℓ → Ord ℓ → Ord ℓ
_+_ a = iter suc a
_*_ a = iter (_+ a) zero
_^_ a = iter (_* a) (suc zero)

lfp : (Ord ℓ → Ord ℓ) → Ord ℓ
lfp f = lim (ℕ.iter f zero)

ψ< : i < ℓ → Ord ℓ → Ord i
ψ< p zero     = lfp (Ω _ ^_)
ψ< p (suc a)  = lfp (ψ< p a ^_)
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

-- n-iteration of ψ₀
ψⁿ : ℕ → Ord₀
ψⁿ = ℕ.iter (ψ₀ ∘ Ω ∘ ordᴰ) zero

ex1 = ψⁿ 1    -- ω
ex2 = ψⁿ 2    -- Buchholz's ordinal
ex3 = ψⁿ 3    -- ψ(Ω_BO)
ex4 = ψⁿ 4    -- ψ(Ω_ψ(Ω_BO))

BTBO : Ord₀
BTBO = lim ψⁿ -- ψ(Ω_Ω)

FGH : Ord₀ → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = ℕ.iter (FGH a) n n
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
