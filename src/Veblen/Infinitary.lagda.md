---
title: 形式化大数数学 (1.4 - 无限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/707292191
---

# 形式化大数数学 (1.4 - 无限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Infinitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Infinitary.lagda.md)  
> 高亮渲染: [Infinitary.html](https://choukh.github.io/agda-googology/Veblen.Infinitary.html)  

```agda
{-# OPTIONS --lossy-unification --rewriting --local-confluence-check #-}
module Veblen.Infinitary where
open import Veblen.Basic public hiding (F)
```

本篇要讲的无限元Veblen函数, 并不是超限元或者说序元 (以序数作为元数) Veblen函数. 我们将踏入这个层次, 但还没有完全覆盖. 从有限到超限的过程中, 有一个里程碑式的层级—— $ω+n$ 元Veblen函数, 我们称为无限元Veblen函数.

## ω元Veblen函数

我们先来搞清楚: 「什么叫 $ω$ 元?」. 首先这决不意味着我们有真无穷的信息, 否则可能就成黑洞了. 也就是说 $ω$ 元里的大部分信息是被「压缩」了的. 如何压缩? 就是用上一篇讲的填零操作 $\overset{.}{0}:A^{→n}→A$ 压缩的.

```agda
import Veblen.Finitary as Fin
open Fin using (_→ⁿ_; _0̇; _0̇,_)
```

也就是说, 我们只有有限个非零参数, 而有无限个零参数. 这就是无限元的真相. 确实, 也只有这样, 才能保证可计算性.

回想我们在首篇定义的 $ω := \lim\text{finord}$. 其中的极限 $\lim$ 相当于一种原语, 它没有进一步的定义. 类型论的规则只不过是保证它可以对应到一种有限的计算过程 (对角化), 而没有公理保证它里面有无穷多的元素, 也不需要此种保证. 无公理类型论中的一切函数都可以看作是某种真有限的计算过程.

回到 $ω$ 元. 上面说到会有无限个零作为参数, 这无限个零肯定不可能排在最前面, 因为这样的话它们就失效了. 也就是说, 必须有一个非零排在无限个零的**前**面. 通常认为, 排在无限之**后**的下一个数是 $ω^+$. 这里的**前后**无关紧要, 可以认为是一回事. 基于此, 我们认为, 其实, 没有 $ω$ 元Veblen函数. 无限元Veblen函数应该是从 $ω^+$ 元开始的.

或者, 我们也可以认为, $ω$ 元Veblen函数其实已经定义完了. 它就是上一篇讲的有限元Veblen函数 $φ_{n}$. 这里违和感的根源在于非形式说法的模糊性. 如果把 $φ_n$ 的 $n$ 看作是任意给定的 (arbitrary), 那么 $φ_{n} : \text{Ord}^{n^+}$ 就是一个真有限元函数. 但如果把 $n$ 看作一个变量, 那么我们认为 $φ_{n} : \prod_{n:ℕ}\text{Ord}^{n^+}$ 是一个无限元函数. 这种意义上的 $φ_{n}$ 我们特别记作 $φ_{\lt ω}$, 以明确区别.

**定义** $ω$ 元序数函数类型

$$
\text{Ord}^{→ω} := \prod_{n:ℕ}\text{Ord}^{n^+}
$$

```agda
Ord→^ω : Set
Ord→^ω = ∀ n → Ord →ⁿ suc n
```

**定义** $ω$ 元Veblen函数

$$
\begin{aligned}
Φ_{\lt ω} &:= Φ : \text{Ord}^{→1} → \text{Ord}^{→ω} \\
φ_{\lt ω} &:= φ : \text{Ord}^{→ω}
\end{aligned}
$$

```agda
module OmegaryVeblen where
  Φ : Ord →ⁿ 1 → Ord→^ω
  Φ = Fin.Φ

  φ : Ord→^ω
  φ = Fin.φ
```

注意我们的下标是一贯的, 它是参数的 (从零开始的) 最大编号, 例如

- $φ_{0}$ 是一元函数, 它有第 $0$ 个参数
- $φ_{1}$ 是二元函数, 它有第 $0$, 第 $1$ 个参数
- ...

也就是说参数的最大编号是元数的直接前驱. 而 $ω$ 没有直接前驱, 所以 $ω$ 元函数的下标不是一个具体的数. 但 $ω⁺$ 元函数的下标将是 $ω$.

- $φ_{\lt ω}$ 是 $ω$ 元函数, 它有第 $0$, 第 $1$, ... 第 $n$ 个参数
- $φ_{ω}$ 是 $ω⁺$ 元函数, 它有第 $0$, 第 $1$, ... 第 $ω$ 个参数
- $φ_{ω⁺}$ 是 $ω⁺⁺$ 元函数, 它有第 $0$, 第 $1$, ... 第 $ω$, 第 $ω⁺$ 个参数
- ...

## ω⁺元Veblen函数

```agda
module OmegaUnaryVeblen where
  module Ltω = OmegaryVeblen
```

$ω^+$ 元Veblen函数具有跟一元函数 $λα,ω^α:\text{Ord}→\text{Ord}$ 同等的地位, 它是新的「梦的开始」. 也因此, 它的构造是特殊的, 在它之前没有直接参考物. 但我们可以如下考虑:

首先, 参考 $n$ 元 $Φ_n$ 的类型

$$
Φ_n : \text{Ord}^{→n^+} → \text{Ord}^{→n^{++}}
$$

对 $ω^+$ 元 $Φ$ 应该有

$$
Φ_ω : \text{Ord}^{→ω} → (\text{Ord} → \text{Ord}^{→ω})
$$

即

$$
Φ_ω : \text{Ord}^{→ω} → (\text{Ord}^{→ω})^{→1}
$$

其输入将会是 $φ_{\lt ω} : \text{Ord}^{→ω}$.

其次, 如果我们希望, 非形式地,

$$
φ_{ω}\kern{0.17em}1\kern{0.17em}0... = \text{SVO} = \lim λn,φ_{n}\kern{0.17em}1\kern{0.17em}\overset{.}{0}
$$

那么 $Φ_{ω}$ 的递归定义的后继步骤应该包含 $\lim$ 的形式, 且我们知道 $\lim$ 必然搭配跳出, 于是有

$$
\text{jump}_1\kern{0.17em}λβ,\lim λn,φ_{ω,α,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0}
$$

其中 $φ_{ω,α} : \text{Ord}^{→ω}$ 是递归的上一步的结果. 注意此处的跳出很特殊, 要从 $1$ 开始, 而不是通常的 $0$ 开始, 以吻合 $\text{SVO}$.

最后, 我们知道 $Φ_n$ 迭代的是 $Φ_{\lt n}$, 于是 $Φ_ω$ 应该迭代 $Φ_{\lt ω}$, 所以有

$$
Φ_{\lt ω}(\text{jump}_1\kern{0.17em}λβ,\lim λn,φ_{ω,α,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0})
$$

这就是后继步骤的定义. 而极限步骤从通常的定义直接推广即可

$$
Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λn,φ_{ω,f\kern{0.17em}n,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0})
$$

完整写出:

**定义** $ω^+$ 元 $Φ_ω : \text{Ord}^{→ω} → (\text{Ord}^{→ω})^{→1}$

$$
\begin{aligned}
Φ_ω\kern{0.17em}F &= \text{rec}\kern{0.17em}F \\
&\quad(λφ_{ω,α},Φ_{\lt ω}(\text{jump}_1\kern{0.17em}λβ,\lim λn,φ_{ω,α,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0})) \\
&\quad(λφ_{ω,f\kern{0.17em}n},Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λn,φ_{ω,f\kern{0.17em}n,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0}))
\end{aligned}
$$

```agda
  Φ : Ord→^ω → Ord→^ω →ⁿ 1
  Φ F = rec F
    (λ φ-α  → Ltω.Φ $ jump⟨ 1 ⟩ λ β → lim λ n → φ-α n β 0̇)
    (λ φ[_] → Ltω.Φ $ jump λ β → lim λ n → φ[ n ] n β 0̇)
```

**定义** $ω^+$ 元Veblen函数 $φ_ω : (\text{Ord}^{→ω})^{→1}$

$$
φ_ω := Φ\kern{0.17em}φ_{\lt ω}
$$

```agda
  φ : Ord→^ω →ⁿ 1
  φ = Φ Ltω.φ
```

**事实** 第一个参数从无效到刚开始生效, 有

$$
\begin{aligned}
φ_ω\kern{0.17em}0 &= φ_{\lt ω} \\
(φ_ω\kern{0.17em}1)_0\kern{0.17em}0 &= \text{SVO}
\end{aligned}
$$

其中 $φ_ω\kern{0.17em}1$ 是一个 $ω$ 元, 即任意 $n^+$ 元函数 $\prod_{n:ℕ}\text{Ord}^{n^+}$, 于是 $(φ_ω\kern{0.17em}1)_0$ 是一个一元函数, 其唯一参数我们填零.

```agda
  φ-0 : φ 0 ≡ Ltω.φ
  φ-0 = refl

  -- 我们会给元数参数加一层括弧以方便辨认.
  φ-1⋯0 : φ 1 (0) 0 ≡ Fin.SVO
  φ-1⋯0 = refl
```

**定义** 用 $ω^+$ 元Veblen函数写出的 $\text{SVO}$

$$
\text{SVO} := (φ_ω\kern{0.17em}1)_0\kern{0.17em}0
$$

```agda
  SVO : Ord
  SVO = φ 1 (0) 0
```

**事实** 以下序数表示都等于 $\text{SVO}$.

$$
\begin{aligned}
(φ_ω\kern{0.17em}1)_1\kern{0.17em}0\kern{0.17em}0 &= \text{SVO} \\
(φ_ω\kern{0.17em}1)_2\kern{0.17em}0\kern{0.17em}0\kern{0.17em}0 &= \text{SVO}
\end{aligned}
$$

```agda
  φ-1⋯0-0 : φ 1 (1) 0 0 ≡ SVO
  φ-1⋯0-0 = refl

  φ-1⋯0-0-0 : φ 1 (2) 0 0 0 ≡ SVO
  φ-1⋯0-0-0 = refl
```

**事实** 如果 $\lt ω$ 位置的参数没有非零, 那么几个零都无所谓.

$$
(φ_ω\kern{0.17em}1)_n\kern{0.17em}\overset{.}{0} = \text{SVO}
$$

```agda
  φ-1⋯ż-z : φ 1 (n) 0̇, 0 ≡ SVO
  φ-1⋯ż-z = refl
```

**定理** 计算模式

$$
\begin{aligned}
&(Φ_ω\kern{0.17em}F\kern{0.17em}α^+)_0\kern{0.17em}0 
&=&
\lim λn,(Φ_ω\kern{0.17em}F\kern{0.17em}α)_n\kern{0.17em}1\kern{0.17em}\overset{.}{0}
\\
&(Φ_ω\kern{0.17em}F\kern{0.17em}α^+)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λn,(Φ_ω\kern{0.17em}F\kern{0.17em}α)_n\kern{0.17em}((Φ_ω\kern{0.17em}F\kern{0.17em}α^+)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+\kern{0.17em}\overset{.}{0}
\\
&(Φ_ω\kern{0.17em}F\kern{0.17em}(\lim f))_0\kern{0.17em}0 
&=&
\lim λn,(Φ_ω\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n))_n\kern{0.17em}\overset{.}{0}
\\
&(Φ_ω\kern{0.17em}F\kern{0.17em}(\lim f))_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λn,(Φ_ω\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n))_n\kern{0.17em}((Φ_ω\kern{0.17em}F\kern{0.17em}(\lim f))_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+\kern{0.17em}\overset{.}{0}
\\
&(Φ_ω\kern{0.17em}F\kern{0.17em}α)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
&=&
\lim λm,(Φ_ω\kern{0.17em}F\kern{0.17em}α)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
\end{aligned}
$$

其中第五条要求前提

$$
(Φ_ω\kern{0.17em}F\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g) = \lim λm,(Φ_ω\kern{0.17em}F\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
$$

```agda
  private variable F : Ord→^ω

  Φ-s⋯ż-z : Φ F (suc α) (0) 0 ≡ lim λ n → Φ F α (n) 1 0̇
  Φ-s⋯ż-z = refl

  Φ-s⋯ż-s : Φ F (suc α) (n) 0̇, suc β ≡ lim λ n → Φ F α (n) (suc (Φ F (suc α) (n) 0̇, β)) 0̇
  Φ-s⋯ż-s = refl

  Φ-l⋯ż-z : Φ F (lim f) (0) 0 ≡ lim λ n → Φ F (f n) (n) 0̇
  Φ-l⋯ż-z = refl

  Φ-l⋯ż-s : Φ F (lim f) (n) 0̇, suc β ≡ lim λ n → Φ F (f n) (n) (suc (Φ F (lim f) (n) 0̇, β)) 0̇
  Φ-l⋯ż-s = refl

  Φ-α⋯ż-l : (Φ F 0 (n) 0̇, lim g) ≡ lim (λ m → Φ F 0 (n) 0̇, g m)
    → Φ F α (n) 0̇, lim g ≡ lim λ m → Φ F α (n) 0̇, g m
  Φ-α⋯ż-l {α = zero} = id
  Φ-α⋯ż-l {α = suc α} _ = refl
  Φ-α⋯ż-l {α = lim x} _ = refl
```

## ω⁺⁺元Veblen函数

```agda
module OmegaBinaryVeblen where
  module Ltω = OmegaryVeblen
  module Eqω = OmegaUnaryVeblen
```

$ω^{++}$ 元相当于二元的地位, 参考二元Veblen函数的定义即可.

**定义** $Φ_{ω^+} : (\text{Ord}^{→ω})^{→1} → (\text{Ord}^{→ω})^{→2}$ 以及 $φ_{ω^+} : (\text{Ord}^{→ω})^{→2}$

$$
\begin{aligned}
Φ_{ω^+}\kern{0.17em}F &:= \text{rec}\kern{0.17em}F \\
&\quad(λφ_{ω^+,α},Φ_{ω}(Φ_{\lt ω}(\text{fixpt}\kern{0.17em}λβ,(φ_{ω^+,α}\kern{0.17em}\beta)_0\kern{0.17em}0))) \\
&\quad(λφ_{ω,f\kern{0.17em}n},Φ_{ω}(Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λn,(φ_{ω,f\kern{0.17em}n}\kern{0.17em}\beta)_0\kern{0.17em}0))) \\
φ_{ω^+} &:= Φ_{ω^+}\kern{0.17em}φ_{ω}
\end{aligned}
$$

```agda
  Φ : Ord→^ω →ⁿ 1 → Ord→^ω →ⁿ 2
  Φ F = rec F
    (λ φ-α → Eqω.Φ $ Ltω.Φ $ fixpt λ β → φ-α β (0) 0)
    (λ φ[_] → Eqω.Φ $ Ltω.Φ $ jump λ β → lim λ n → φ[ n ] β (0) 0)

  φ : Ord→^ω →ⁿ 2
  φ = Φ Eqω.φ
```

**定理** 计算模式

$$
\begin{aligned}
&(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0)_0\kern{0.17em}0
&=&
(λβ,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β)_0\kern{0.17em}0)^ω\kern{0.17em}0
\\
&(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
(λβ,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β)_0\kern{0.17em}0)^ω\kern{0.17em}((Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+
\\
&(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0)_0\kern{0.17em}0
&=&
\lim λm,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}0)_0\kern{0.17em}0
\\
&(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λm,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}((Φ_{ω^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+)_0\kern{0.17em}0
\\
&(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
&=&
\lim λm,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em})_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
\end{aligned}
$$

其中第五条要求前提

$$
(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g) = \lim λm,(Φ_{ω^+}\kern{0.17em}F\kern{0.17em}0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
$$

```agda
  private variable F : Ord→^ω →ⁿ 1

  Φ-s-z⋯ż-z : Φ F (suc α) 0 (0) 0 ≡ iterω (λ β → Φ F α β (0) 0) 0
  Φ-s-z⋯ż-z = refl

  Φ-s-z⋯ż-s : Φ F (suc α) 0 (n) 0̇, suc β ≡ iterω (λ β → Φ F α β (0) 0) (suc (Φ F (suc α) 0 (n) 0̇, β))
  Φ-s-z⋯ż-s = refl

  Φ-l-z⋯ż-z : Φ F (lim f) 0 (0) 0 ≡ lim λ m → Φ F (f m) 0 (0) 0
  Φ-l-z⋯ż-z = refl

  Φ-l-z⋯ż-s : Φ F (lim f) 0 (n) 0̇, suc β ≡ lim λ m → Φ F (f m) (suc (Φ F (lim f) 0 (n) 0̇, β)) (0) 0
  Φ-l-z⋯ż-s = refl

  Φ-α-z⋯ż-l : Φ F 0 0 (n) 0̇, lim g ≡ lim (λ m → Φ F 0 0 (n) 0̇, g m)
    → Φ F α 0 (n) 0̇, lim g ≡ lim λ m → Φ F α 0 (n) 0̇, g m
  Φ-α-z⋯ż-l {α = zero} = id
  Φ-α-z⋯ż-l {α = suc _} _ = refl
  Φ-α-z⋯ż-l {α = lim _} _ = refl
```

## ω倍数元函数类型

我们继续进发. 仿照 $ω$ 元函数类型的定义, 我们可以定义 $ω$ 倍数元函数类型.

**定义** $ω\cdot n$ 元函数类型 $\text{Ord}^{→ω\cdot n}$

$$
\begin{aligned}
\text{Ord}^{→ω\cdot 0} &:= \text{Ord} \\
\text{Ord}^{→ω\cdot m^+} &:= \prod_{n:ℕ}(\text{Ord}^{→ω\cdot m})^{→n^+}
\end{aligned}
$$

```agda
Ord→^ω* : ℕ → Set
Ord→^ω* zero = Ord
Ord→^ω* (suc m) = ∀ n → Ord→^ω* m →ⁿ suc n
```

**例**

$$
\begin{aligned}
\text{Ord}^{→ω\cdot 0} &= \text{Ord} \\
\text{Ord}^{→ω\cdot 1} &= \text{Ord}^{→ω} \\
\text{Ord}^{→ω\cdot 2} &= \prod_{n:ℕ}(\text{Ord}^{→ω\cdot 1})^{→n^+}
\end{aligned}
$$

```agda
_ : Ord→^ω* 0 ≡ Ord
_ = refl

_ : Ord→^ω* 1 ≡ Ord→^ω
_ = refl

_ : Ord→^ω* 2 ≡ ∀ n → Ord→^ω* 1 →ⁿ suc n
_ = refl
```

**定义** 跨极限填零 $(λF,F\kern{0.17em}0...) : \text{Ord}^{→ω\cdot m}→\text{Ord}$

$$
\begin{aligned}
(F:\text{Ord}^{→ω\cdot 0})\kern{0.17em}0... &:= F \\
(F:\text{Ord}^{→ω\cdot m^+})\kern{0.17em}0... &:= F_0\kern{0.17em}0\kern{0.17em}0...
\end{aligned}
$$

```agda
_0⋯ : Ord→^ω* n → Ord
_0⋯ {n = zero} = id
_0⋯ {n = suc _} F = F (0) 0 0⋯
```

**定义** 极限内填零接跨极限填零 $(λF,F\kern{0.17em}\overset{.}{0}...) : (\text{Ord}^{→ω\cdot m})^{→n}→\text{Ord}$

$$
\begin{aligned}
(F:\text{Ord}^{→ω\cdot 0})\kern{0.17em}\overset{.}{0}... &:= F \\
(F:\text{Ord}^{→ω\cdot m^+})\kern{0.17em}\overset{.}{0}... &:= (F\kern{0.17em}\overset{.}{0})_0\kern{0.17em}0\kern{0.17em}\overset{.}{0}...
\end{aligned}
$$

```agda
_0̇⋯ : Ord→^ω* m →ⁿ n → Ord
_0̇⋯ {m = zero} F = F 0̇
_0̇⋯ {m = suc _} F = (F 0̇) (0) 0 0̇⋯
```

## ω2 元Veblen函数

```agda
module DoubleOmegaryVeblen where
  module Ltω = OmegaryVeblen
  module Eqω = OmegaUnaryVeblen
  module Bin = OmegaBinaryVeblen
```

$ω\cdot 2$ 元相当于二元的地位, 参考二元Veblen函数的定义即可.

**定义** 互递归定义

$$
\begin{aligned}
Φ_{\lt ω2,n} &: (\text{Ord}^{→ω})^{→n^+} → (\text{Ord}^{→ω})^{→n^{++}} \\
Φ_{\lt ω2} &: (\text{Ord}^{→ω})^{→1} → \text{Ord}^{→ω\cdot 2}
\end{aligned}
$$

为

$$
\begin{aligned}
Φ_{\lt ω2,n}\kern{0.17em}F &:= \text{rec}\kern{0.17em}F \\
&\quad(λφ_{\lt ω2,n^+,α},Φ_{\lt ω2}^n(Φ_{ω}(Φ_{\lt ω}(\text{fixpt}\kern{0.17em}λβ,φ_{\lt ω2,n^+,α}\kern{0.17em}β\kern{0.17em}\overset{.}{0}...))))\\
&\quad(λφ_{\lt ω2,n^+,f\kern{0.17em}m},Φ_{\lt ω2}^n(Φ_{ω}(Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λm,φ_{\lt ω2,n^+,f\kern{0.17em}m}\kern{0.17em}β\kern{0.17em}\overset{.}{0}...)))) \\
Φ_{\lt ω2}^0\kern{0.17em}F &:= F \\
Φ_{\lt ω2}^{n^+}\kern{0.17em}F &:= Φ_{\lt ω2,n}(Φ_{\lt ω2}^n\kern{0.17em}F)
\end{aligned}
$$

```agda
  Φₙ : Ord→^ω →ⁿ suc n → Ord→^ω →ⁿ 2+ n
  Φ : Ord→^ω →ⁿ 1 → Ord→^ω* 2

  Φₙ {n} F = rec F
    (λ φ-α → Φ (Eqω.Φ $ Ltω.Φ $ fixpt λ β → φ-α β 0̇⋯) (n))
    (λ φ[_] → Φ (Eqω.Φ $ Ltω.Φ $ jump λ β → lim λ m → φ[ m ] β 0̇⋯) (n))

  Φ F (zero) = F
  Φ F ((suc n)) = Φₙ (Φ F (n))
```

**定义** $φ_{\lt ω2} : \prod_{n:ℕ}(\text{Ord}^{→ω})^{→n^+}$

$$
φ_{\lt ω2} := Φ_{\lt ω2}\kern{0.17em}φ_{ω}
$$

```agda
  φ : ∀ n → Ord→^ω →ⁿ suc n
  φ = Φ Eqω.φ
```

**事实** $ω + n^{++}$ 元Veblen函数 $φ_{ω,n^+}$ 等于对 $ω + n^+$ 元Veblen函数 $φ_{ω,n}$ 做一次 $Φ_{\lt ω2,n}$, 并且首位输入零的话就等于 $φ_{ω,n}$.

$$
\begin{aligned}
φ_{ω,n^+} &= Φ_{\lt ω2,n}\kern{0.17em}φ_{ω,n} \\
φ_{ω,n^+} 0 &= φ_{ω,n}
\end{aligned}
$$
```agda
  Φ-φ : φ ((suc n)) ≡ Φₙ (φ (n))
  Φ-φ = refl

  φ-0 : φ ((suc n)) 0 ≡ φ (n)
  φ-0 = refl
```

**例**

$$
\begin{aligned}
φ_{\lt ω2,0} &= φ_{ω} \\
φ_{\lt ω2,1} &= φ_{ω^+} \\
\end{aligned}
$$

```agda
  φ₀ : φ (0) ≡ Eqω.φ
  φ₀ = refl

  φ₁ : φ (1) ≡ Bin.φ
  φ₁ = refl
```

**引理** 对任意 $F : (\text{Ord}^{→ω})^{→1}$, 有

$$
(Φ_{\lt ω2}\kern{0.17em}F)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} = F
$$

```agda
  private variable F : Ord→^ω →ⁿ 1

  Φ-ż-α : Φ F (n) 0̇,_ ≡ F
  Φ-ż-α {n = zero} = refl
  Φ-ż-α {n = suc n} = Φ-ż-α {n = n}
  {-# REWRITE Φ-ż-α #-}
```

将该引理声明为新的重写规则, 可以立即证明:

**定理** 计算模式

$$
\begin{aligned}
&(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}0)\kern{0.17em}\overset{.}{0}...
&=&
(λβ,Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0}...)^ω\kern{0.17em}0
\\
&(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
(λβ,Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0}...)^ω\kern{0.17em}((Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+
\\
&(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}0)\kern{0.17em}\overset{.}{0}...
&=&
\lim λm,Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}0\kern{0.17em}\overset{.}{0}...
\\
&(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λm,(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}((Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+)\kern{0.17em}\overset{.}{0}...
\\
&(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
&=&
\lim λk,(Φ_{\lt ω2}^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}\overset{.}{0}\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}k)
\end{aligned}
$$

其中第五条要求前提

$$
(F\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g) = \lim λk,(F\kern{0.17em}0)_m\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}k)
$$

```agda
  Φ-s-ż⋯ż-z : (Φ F ((suc n)) (suc α) 0̇, 0) 0⋯
    ≡ iterω (λ β → Φ F ((suc n)) α β 0̇⋯) 0
  Φ-s-ż⋯ż-z = refl

  Φ-s-ż⋯ż-s : (Φ F ((suc n)) (suc α) 0̇, 0) (m) 0̇, suc β
    ≡ iterω (λ β → Φ F ((suc n)) α β 0̇⋯) (suc ((Φ F (_) (suc α) 0̇, 0) (m) 0̇, β))
  Φ-s-ż⋯ż-s = refl

  Φ-l-ż⋯ż-z : (Φ F ((suc n)) (lim f) 0̇, 0) 0⋯
    ≡ lim λ m → Φ F ((suc n)) (f m) 0 0̇⋯
  Φ-l-ż⋯ż-z = refl

  Φ-l-ż⋯ż-s : (Φ F ((suc n)) (lim f) 0̇, 0) (m) 0̇, suc β
    ≡ lim λ m → Φ F ((suc n)) (f m) (suc ((Φ F ((suc n)) (lim f) 0̇, 0) (m) 0̇, β)) 0̇⋯
  Φ-l-ż⋯ż-s = refl

  Φ-α-ż⋯ż-l : F 0 (m) 0̇, lim g ≡ lim (λ k → F 0 (m) 0̇, g k)
    → (Φ F ((suc n)) α 0̇, 0) (m) 0̇, lim g ≡ lim λ k → (Φ F ((suc n)) α 0̇, 0) (m) 0̇, g k
  Φ-α-ż⋯ż-l {α = zero} = id
  Φ-α-ż⋯ż-l {α = suc _} _ = refl
  Φ-α-ż⋯ż-l {α = lim _} _ = refl
```

**定义** 第二代 $\text{SVO}$

$$
\text{SVO} := \lim λn,φ_{\lt ω2,n}\kern{0.17em}1\kern{0.17em}\overset{.}{0}...
$$

```agda
  SVO₂ : Ord
  SVO₂ = lim λ n → φ (n) 1 0̇⋯
```

## (ω2)⁺元Veblen函数

```agda
module DoubleOmegaUnaryVeblen where
  module Ltω = OmegaryVeblen
  module Eqω = OmegaUnaryVeblen
  module Ltω2 = DoubleOmegaryVeblen
```

$(ω\cdot 2)^+$ 元相当于 $ω^+$ 元的地位, 参考 $ω^+$ 元Veblen函数的定义即可.

**定义** $Φ_{ω2} : (\text{Ord}^{→ω\cdot 2})^{→2} → (\text{Ord}^{→ω\cdot 2})^{→1}$ 以及 $φ_{ω2} : (\text{Ord}^{→ω\cdot 2})^{→1}$

$$
\begin{aligned}
Φ_{ω2}\kern{0.17em}F &:= \text{rec}\kern{0.17em}F \\
&\quad(λφ_{ω2,α},Φ_{\lt ω2}(Φ_{ω}(Φ_{\lt ω}(\text{jump}_1\kern{0.17em}λβ,\lim λn,φ_{ω2,α,n}\kern{0.17em}β\kern{0.17em}\overset{.}{0}...)))) \\
&\quad(λφ_{ω2,f\kern{0.17em}n},Φ_{\lt ω2}(Φ_{ω}(Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λn,φ_{ω2,f\kern{0.17em}n,n}\kern{0.17em}β\kern{0.17em}\overset{.}{0}...)))) \\
φ_{ω2} &:= Φ_{ω2}\kern{0.17em}φ_{\lt ω2}
\end{aligned}
$$

```agda
  Φ : Ord→^ω* 2 → Ord→^ω* 2 →ⁿ 1
  Φ F = rec F
    (λ φ-α  → Ltω2.Φ $ Eqω.Φ $ Ltω.Φ $ jump⟨ 1 ⟩ λ β → lim λ n → φ-α n β 0̇⋯)
    (λ φ[_] → Ltω2.Φ $ Eqω.Φ $ Ltω.Φ $ jump λ β → lim λ n → φ[ n ] n β 0̇⋯)

  φ : Ord→^ω* 2 →ⁿ 1
  φ = Φ Ltω2.φ
```

**事实** 第一个参数从无效到刚开始生效, 有

$$
\begin{aligned}
φ_{ω2}\kern{0.17em}0 &= φ_{\lt ω2} \\
φ_{ω2}\kern{0.17em}1\kern{0.17em}\overset{.}{0}... &= \text{SVO}_2
\end{aligned}
$$

```agda
  φ-0 : φ 0 ≡ Ltω2.φ
  φ-0 = refl

  φ-1⋯0⋯0 : φ 1 0⋯ ≡ Ltω2.SVO₂
  φ-1⋯0⋯0 = refl
```

**定理** 计算模式

$$
\begin{aligned}
&Φ_{ω2}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}...
&=&
\lim λn,(Φ_{ω2}\kern{0.17em}F\kern{0.17em}α\kern{0.17em})_n\kern{0.17em}1\kern{0.17em}\overset{.}{0}...
\\
&((Φ_{ω2}\kern{0.17em}F\kern{0.17em}α^+)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λn,(Φ_{ω2}\kern{0.17em}F\kern{0.17em}α\kern{0.17em})_n\kern{0.17em}(((Φ_{ω2}\kern{0.17em}F\kern{0.17em}α^+)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+
\\
&Φ_{ω2}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}...
&=&
\lim λn,(Φ_{ω2}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n))_n\kern{0.17em}0\kern{0.17em}\overset{.}{0}...
\\
&((Φ_{ω2}\kern{0.17em}F\kern{0.17em}(\lim f))_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+
&=&
\lim λn,(Φ_{ω2}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n))_n\kern{0.17em}(((Φ_{ω2}\kern{0.17em}F\kern{0.17em}(\lim f))_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+\kern{0.17em}\overset{.}{0}...
\\
&((Φ_{ω2}\kern{0.17em}F\kern{0.17em}α)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
&=&
\lim λm,((Φ_{ω2}\kern{0.17em}F\kern{0.17em}α)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
\end{aligned}
$$

其中第五条要求前提

$$
((F\kern{0.17em}0)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g) = \lim λm,((F\kern{0.17em}0)_0\kern{0.17em}0)_n\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
$$

```agda
  private variable F : Ord→^ω* 2

  Φ-s⋯ż⋯ż-z : Φ F (suc α) 0⋯ ≡ lim λ n → Φ F α (n) 1 0̇⋯
  Φ-s⋯ż⋯ż-z = refl

  Φ-s⋯ż⋯ż-s : Φ F (suc α) (0) 0 (n) 0̇, suc β ≡ lim λ n → Φ F α (n) (suc (Φ F (suc α) (0) 0 (n) 0̇, β)) 0̇⋯
  Φ-s⋯ż⋯ż-s = refl

  Φ-l⋯ż⋯ż-z : Φ F (lim f) 0⋯ ≡ lim λ n → Φ F (f n) (n) 0 0̇⋯
  Φ-l⋯ż⋯ż-z = refl

  Φ-l⋯ż⋯ż-s : Φ F (lim f) (0) 0 (n) 0̇, suc β ≡ lim λ n → Φ F (f n) (n) (suc (Φ F (lim f) (0) 0 (n) 0̇, β)) 0̇⋯
  Φ-l⋯ż⋯ż-s = refl

  Φ-α⋯ż⋯ż-l : (Φ F 0 (0) 0 (n) 0̇, lim g) ≡ lim (λ m → (Φ F 0 (0) 0 (n) 0̇, g m))
    → Φ F α (0) 0 (n) 0̇, lim g ≡ lim λ m → (Φ F α (0) 0 (n) 0̇, g m)
  Φ-α⋯ż⋯ż-l {α = zero} = id
  Φ-α⋯ż⋯ż-l {α = suc α} _ = refl
  Φ-α⋯ż⋯ż-l {α = lim x} _ = refl
```

## 总结

现在我们可以总结后继元与极限元的规律了. 设 $μ$ 为任意极限序数, $ν$ 是下一个极限序数.

- 极限阶段: $μ^+$ 元由 $Φ_{μ}$ 给出, 它是我们一直说的「梦的开始」, 其定义的特征是 $\text{jump}_1$ (一元除外)
  - 一元时是 $λα,ω^α$
  - $ω^+$ 元由 $Φ_{ω}$ 给出
  - $(ω2)^+$ 元由 $Φ_{ω2}$ 给出
  - ...
- 后继阶段: $μ^{++}$ 元到 $\lt ν$ 由 $Φ_{\lt ν}$ 给出, 其定义的特征是互递归
  - $ω$ 元由 $Φ_{\lt ω}$ 给出
  - $ω2$ 元由 $Φ_{\lt ω2}$ 给出
  - ...
- 极限阶段: $ν^{+}$ 元由 $Φ_{ν}$ 给出
- ...

下一篇将正式推广到任意序数元.

