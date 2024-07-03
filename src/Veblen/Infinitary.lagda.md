---
title: 形式化大数数学 (1.4 - 无限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
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

或者, 我们也可以认为, $ω$ 元Veblen函数其实已经定义完了. 它就是上一篇讲的有限元Veblen函数 $φ_{n}$. 这里违和感的根源在于非形式说法的模糊性. 如果把 $φ_n$ 的 $n$ 看作是任意给定的 (arbitrary), 那么 $φ_{n} : \text{Ord}^{n^+}$ 就是一个真有限元函数. 但如果把 $n$ 看作一个变量, 那么我们认为 $φ_{n} : \Pi_{n:ℕ}\text{Ord}^{n^+}$ 是一个无限元函数. 这种意义上的 $φ_{n}$ 我们特别记作 $φ_{\lt ω}$, 以明确区别.

**定义** $ω$ 元, $ω^+$ 元和 $ω^{++}$ 元序数函数类型

$$
\begin{aligned}
\text{Ord}^{→ω} &:= \Pi_{n:ℕ}\text{Ord}^{n^+} \\
\text{Ord}^{→ω^+} &:= \text{Ord} → \text{Ord}^{→ω} \\
\text{Ord}^{→ω^{++}} &:= \text{Ord} → \text{Ord}^{→ω^+}
\end{aligned}
$$

```agda
Ord→^ω Ord→^ω⁺ Ord→^ω⁺⁺ : Set
Ord→^ω = (n : ℕ) → Ord →ⁿ suc n
Ord→^ω⁺ = Ord → Ord→^ω
Ord→^ω⁺⁺ = Ord → Ord→^ω⁺
```

**定义** $ω$ 元Veblen函数

$$
\begin{aligned}
Φ_{\lt ω} &:= Φ^n : \text{Ord}^{→1} → \text{Ord}^{→ω} \\
φ_{\lt ω} &:= φ_n : \text{Ord}^{→ω}
\end{aligned}
$$

```agda
module OmegaryVeblen where
  Φ : Ord →ⁿ 1 → Ord→^ω
  Φ F n = Fin.Φⁿ {n} F

  φ : Ord→^ω
  φ n = Fin.φ {n}
```

注意我们的下标是一贯的:

- $φ_{0}$ 是一元函数
- $φ_{1}$ 是二元函数
- ...

也就是说下标是元数的直接前驱, 但 $ω$ 没有直接前驱, 所以 $ω$ 元函数的下标不是一个具体的数. 但 $ω⁺$ 元函数的下标将是 $ω$.

- $φ_{\lt ω}$ 是 $ω$ 元函数
- $φ_{ω}$ 是 $ω⁺$ 元函数
- $φ_{ω⁺}$ 是 $ω⁺⁺$ 元函数
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

对 $Φ_ω$ 应该有

$$
Φ_ω : \text{Ord}^{→ω} → (\text{Ord} → \text{Ord}^{→ω})
$$

```agda
  Φ : Ord→^ω → Ord→^ω⁺
```

其输入将会是 $φ_{\lt ω} : \text{Ord}^{→ω}$.

其次, 如果我们希望

$$
φ_{ω}\kern{0.17em}1\kern{0.17em}\overset{.}{0} = \text{SVO} = \lim λn,φ_{n}\kern{0.17em}1\kern{0.17em}\overset{.}{0}
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

**定义** $Φ_{ω}$

$$
\begin{aligned}
Φ_{ω}\kern{0.17em}F &= \text{rec}\kern{0.17em}F \\
&\quad(λφ_{ω,α},Φ_{\lt ω}(\text{jump}_1\kern{0.17em}λβ,\lim λn,φ_{ω,α,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0})) \\
&\quad(λφ_{ω,f\kern{0.17em}n},Φ_{\lt ω}(\text{jump}\kern{0.17em}λβ,\lim λn,φ_{ω,f\kern{0.17em}n,n}\kern{0.17em}\beta\kern{0.17em}\overset{.}{0}))
\end{aligned}
$$

```agda
  Φ F = rec F
    (λ φ-α  → Ltω.Φ $ jump⟨ 1 ⟩ λ β → lim λ n → φ-α n β 0̇)
    (λ φ[_] → Ltω.Φ $ jump λ β → lim λ n → φ[ n ] n β 0̇)
```

```agda
  φ : Ord → Ord→^ω
  φ = Φ Ltω.φ
```

```agda
  φ-0 : φ 0 ≡ Ltω.φ
  φ-0 = refl

  φ-1⋯0 : φ 1 _ 0 ≡ Fin.SVO
  φ-1⋯0 = refl
```

```agda
  φ-1⋯0-0 : φ 1 _ 0 0 ≡ Fin.SVO
  φ-1⋯0-0 = refl

  φ-1⋯0-0-0 : φ 1 _ 0 0 0 ≡ Fin.SVO
  φ-1⋯0-0-0 = refl
```

```agda
  φ-1⋯ż-z : φ 1 (n) 0̇, 0 ≡ Fin.SVO
  φ-1⋯ż-z = refl
```

```agda
  private variable F : Ord→^ω

  Φ-s⋯ż-z : Φ F (suc α) _ 0 ≡ lim λ n → Φ F α (n) 1 0̇
  Φ-s⋯ż-z = refl

  Φ-s⋯ż-s : Φ F (suc α) (n) 0̇, suc β ≡ lim λ n → Φ F α (n) (suc (Φ F (suc α) (n) 0̇, β)) 0̇
  Φ-s⋯ż-s = refl

  Φ-l⋯ż-z : Φ F (lim f) _ 0 ≡ lim λ n → Φ F (f n) (n) 0̇
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

```agda
  Φ : Ord→^ω⁺ → Ord→^ω⁺⁺
  Φ F = rec F
    (λ φ-α → Eqω.Φ $ Ltω.Φ $ fixpt λ β → φ-α β _ 0)
    (λ φ[_] → Eqω.Φ $ Ltω.Φ $ jump λ β → lim λ m → φ[ m ] β _ 0)

  φ : Ord→^ω⁺⁺
  φ = Φ Eqω.φ
```

```agda
  private variable F : Ord→^ω⁺

  Φ-s-z⋯ż-z : Φ F (suc α) 0 _ 0 ≡ iterω (λ β → Φ F α β _ 0) 0
  Φ-s-z⋯ż-z = refl

  Φ-s-z⋯ż-s : Φ F (suc α) 0 (n) 0̇, suc β ≡ iterω (λ β → Φ F α β _ 0) (suc (Φ F (suc α) 0 (n) 0̇, β))
  Φ-s-z⋯ż-s = refl

  Φ-l-z⋯ż-z : Φ F (lim f) 0 _ 0 ≡ lim λ m → Φ F (f m) 0 _ 0
  Φ-l-z⋯ż-z = refl

  Φ-l-z⋯ż-s : Φ F (lim f) 0 (n) 0̇, suc β ≡ lim λ m → Φ F (f m) (suc (Φ F (lim f) 0 (n) 0̇, β)) _ 0
  Φ-l-z⋯ż-s = refl

  Φ-α-z⋯ż-l : Φ F 0 0 (n) 0̇, lim g ≡ lim (λ m → Φ F 0 0 (n) 0̇, g m)
    → Φ F α 0 (n) 0̇, lim g ≡ lim λ m → Φ F α 0 (n) 0̇, g m
  Φ-α-z⋯ż-l {α = zero} = id
  Φ-α-z⋯ż-l {α = suc _} _ = refl
  Φ-α-z⋯ż-l {α = lim _} _ = refl
```

## 2ω元Veblen函数

```agda
module DoubleOmegaryVeblen where
  module Ltω = OmegaryVeblen
  module Eqω = OmegaUnaryVeblen
  module Bin = OmegaBinaryVeblen
```

```agda
  Φₙ : Ord→^ω →ⁿ suc n → Ord→^ω →ⁿ 2+ n
  Φⁿ : Ord→^ω →ⁿ 1 → Ord→^ω →ⁿ suc n
```

```agda
  Φₙ F = rec F
    (λ φ-α → Φⁿ $ Eqω.Φ $ Ltω.Φ $ fixpt λ β → (φ-α β 0̇) _ 0)
    (λ φ[_] → Φⁿ $ Eqω.Φ $ Ltω.Φ $ jump λ β → lim λ m → (φ[ m ] β 0̇) _ 0)
```

```agda
  Φⁿ {n = zero} = id
  Φⁿ {n = suc n} F = Φₙ (Φⁿ F)
```

```agda
  φ : Ord→^ω →ⁿ suc n
  φ = Φⁿ Eqω.φ
```

```agda
  Φ-φ : φ {suc n} ≡ Φₙ (φ {n})
  Φ-φ = refl

  φ-0 : φ {suc n} 0 ≡ φ {n}
  φ-0 = refl
```

```agda
  φ₀ : φ {0} ≡ Eqω.φ
  φ₀ = refl

  φ₁ : φ {1} ≡ Bin.φ
  φ₁ = refl
```

```agda
  private variable F : Ord→^ω →ⁿ 1

  Φ-ż-α : Φⁿ {n} F 0̇,_ ≡ F
  Φ-ż-α {n = zero} = refl
  Φ-ż-α {n = suc n} = Φ-ż-α {n}
  {-# REWRITE Φ-ż-α #-}
```

```agda
  Φ-s-ż⋯ż-z : (Φⁿ {suc n} F (suc α) 0̇, 0) _ 0
    ≡ iterω (λ β → (Φⁿ {suc n} F α β 0̇) _ 0) 0
  Φ-s-ż⋯ż-z = refl

  Φ-s-ż⋯ż-s : (Φⁿ {suc n} F (suc α) 0̇, 0) (m) 0̇, suc β
    ≡ iterω (λ β → (Φⁿ {suc n} F α β 0̇) _ 0) (suc ((Φⁿ F (suc α) 0̇, 0) (m) 0̇, β))
  Φ-s-ż⋯ż-s = refl

  Φ-l-ż⋯ż-z : (Φⁿ {suc n} F (lim f) 0̇, 0) _ 0
    ≡ lim λ m → (Φⁿ {suc n} F (f m) 0 0̇) _ 0
  Φ-l-ż⋯ż-z = refl

  Φ-l-ż⋯ż-s : (Φⁿ {suc n} F (lim f) 0̇, 0) (m) 0̇, suc β
    ≡ lim λ m → (Φⁿ {suc n} F (f m) (suc ((Φⁿ {suc n} F (lim f) 0̇, 0) (m) 0̇, β)) 0̇) _ 0
  Φ-l-ż⋯ż-s = refl

  Φ-α-ż⋯ż-l : F 0 (m) 0̇, lim g ≡ lim (λ k → F 0 (m) 0̇, g k)
    → (Φⁿ {suc n} F α 0̇, 0) (m) 0̇, lim g ≡ lim λ k → (Φⁿ {suc n} F α 0̇, 0) (m) 0̇, g k
  Φ-α-ż⋯ż-l {α = zero} = id
  Φ-α-ż⋯ż-l {α = suc _} _ = refl
  Φ-α-ż⋯ż-l {α = lim _} _ = refl
```

## (2ω)⁺元Veblen函数

## 3ω元Veblen函数
