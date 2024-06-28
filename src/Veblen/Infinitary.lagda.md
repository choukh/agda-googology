---
title: 形式化大数数学 (1.4 - 无限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.4 - 无限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Infinitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Infinitary.lagda.md)  
> 高亮渲染: [Infinitary.html](https://choukh.github.io/agda-googology/Veblen.Infinitary.html)  

```agda
module Veblen.Infinitary where
open import Veblen.Basic public
```

本篇要讲的无限元Veblen函数, 并不是超限元或者说序元 (以序数作为元数) Veblen函数. 我们将踏入这个层次, 但还没有完全覆盖. 从有限到超限的过程中, 有一个里程碑式的层级—— $ω+n$ 元Veblen函数, 我们称为无限元Veblen函数.

## ω元Veblen函数

我们先来搞清楚: 「什么叫 $ω$ 元?」. 首先这决不意味着我们有真无穷的信息, 否则可能成黑洞了. 所以 $ω$ 元里的大部分信息是被「压缩」了的. 如何压缩? 就是用上一篇讲的填零操作 $\overset{.}{0}:A^{→n}→A$ 压缩的.

```agda
import Veblen.Finitary as Fin
open Fin using (_→ⁿ_; _0̇)
```

也就是说, 我们只有有限个非零参数, 而有无限个零参数. 这就是无限元的真相. 确实, 也只有这样, 才能保证可计算性.

回想我们在首篇定义的 $ω := \lim\text{finord}$. 其中的极限 $\lim$ 相当于一种原语, 它没有进一步的定义. 类型论的规则只不过是保证它可以对应到一种有限的计算过程 (对角化), 而没有公理保证它里面有无穷多的元素, 也不需要此种保证. 无公理类型论中的一切函数都可以看作是某种真有限的计算过程.

回到 $ω$ 元. 上面说到会有无限个零作为参数, 这无限个零肯定不可能排在最前面, 因为这样的话它们就失效了. 也就是说, 必须有一个非零排在无限个零的**前**面. 通常认为, 排在无限之**后**的下一个就是 $ω^+$. 这里的**前后**无关紧要, 可以认为是一回事. 基于此, 我们认为, 其实, 没有 $ω$ 元Veblen函数. 无限元Veblen函数应该是从 $ω^+$ 元开始的.

或者, 我们也可以认为, $ω$ 元Veblen函数其实已经定义完了. 它就是上一篇讲的有限元Veblen函数. 正因为这里是有限和无限的微妙分界线, 我们认为很重要, 所以专门讲了一小节.

**定义** $ω$ 元和 $ω^+$ 元序数函数类型

$$
\begin{aligned}
\text{Ord}^{→ω} &:= \Pi_{n:ℕ}\text{Ord}^{n^+} \\
\text{Ord}^{→ω^+} &:= \text{Ord} → \text{Ord}^{→ω}
\end{aligned}
$$

```agda
Ord→^ω Ord→^ω⁺ : Set
Ord→^ω = ∀ {n} → Ord →ⁿ suc n
Ord→^ω⁺ = Ord → Ord→^ω
```

**定义** $ω$ 元Veblen函数

$$
φ_ω := φ_n : \text{Ord}^{→ω}
$$

```agda
module OmegaryVeblen where
  φ : Ord→^ω
  φ = Fin.φ
```

## ω⁺元Veblen函数

$ω^+$ 元Veblen函数具有跟一元函数 $λα,ω^α:\text{Ord}→\text{Ord}$ 同等的地位, 它是新的梦的开始. 也因此, 它的构造是特殊的, 在它之前没有任何参考物.

但是 $\text{SVO}$ 的构造可以帮助反推其定义. 如果我们希望

$$
φ_{ω^+}\kern{0.17em}1\kern{0.17em}\overset{.}{0} = \text{SVO} = \lim λn,φ_{n}\kern{0.17em}1\kern{0.17em}\overset{.}{0}
$$

那么 $φ_{ω^+}$ 的递归定义的后继步骤也必须具有 $\lim$ 的形式, 这一点与任意 $φ_{\lt ω}$ 都不同.

```agda
module OmegaUnaryVeblen where

  Φ : Ord→^ω → Ord → Ord→^ω
  Φ F = rec F
    (λ φ-μ  → Fin.Φⁿ $ jump λ α → lim λ n → φ-μ {n} (suc α) 0̇)
    (λ φ[_] → Fin.Φⁿ $ jump λ α → lim λ n → φ[ n ] (suc α))

  φ : Ord → Ord→^ω
  φ = Φ Fin.φ
```

```agda
  φ-0 : φ 0 {n} ≡ Fin.φ
  φ-0 = refl
```

```agda
  φ-1⋯0 : φ 1 0 ≡ Fin.SVO
  φ-1⋯0 = refl

  φ-1⋯0-0 : φ 1 0 0 ≡ Fin.SVO
  φ-1⋯0-0 = refl

  φ-1⋯0-0-0 : φ 1 0 0 0 ≡ Fin.SVO
  φ-1⋯0-0-0 = refl
```

## ω⁺⁺元Veblen函数

```agda
module OmegaBinaryVeblen where

  Φ : Ord→^ω⁺ → Ord → Ord→^ω⁺
  Φ F = rec F
    {!   !}
    {!   !}
```

## 2ω元Veblen函数

## (2ω)⁺元Veblen函数

## 3ω元Veblen函数
