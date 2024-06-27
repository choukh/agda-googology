---
title: 形式化大数数学 (1.2 - Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/705436498
---

# 形式化大数数学 (1.2 - Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Multinary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Multinary.lagda.md)  
> 高亮渲染: [Multinary.html](https://choukh.github.io/agda-googology/Veblen.Multinary.html)  

```agda
module Veblen.Multinary where
open import Veblen.Basic public
```

## 综述

前篇讲了Veblen层级的构造需要的三个高阶函数

1. 无穷迭代 $λF,F^\omega$
2. 跳出运算 $\text{jump}$
3. 不动点的枚举 $\text{fixpt}$

以及 $\varepsilon, \zeta, \eta$ 函数的定义

$$
\begin{aligned}
ε &:= \text{fixpt}\kern{0.17em}λα,ω\kern{0.17em}^α \\
ζ &:= \text{fixpt}\kern{0.17em}ε \\
η &:= \text{fixpt}\kern{0.17em}ζ
\end{aligned}
$$

观察这些定义的形式, 不难发现, 很自然地, 构造更大序数的下一步操作是迭代高阶函数 $\text{fixpt}$ 本身. 这要求一个更高阶的函数 $Φ_2$, 然后我们会想要再次迭代这个更高阶的函数, 这又要求一个更更高阶的函数 $Φ_3$, 乃至 $Φ_4$, 以此类推.

- $Φ_2:(\text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_3:(\text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_4:(\text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- ...

回想梦的开始 $λα,ω\kern{0.17em}^α : \text{Ord} → \text{Ord}$, 把它记作 $\varphi_1$.

- 从 $\varphi_1$ 开始, 用 $Φ_2$ 迭代 $\text{fixpt}$, 得到的函数叫做二元Veblen函数 $\varphi_2 : \text{Ord} → \text{Ord} → \text{Ord}$
- 从 $\varphi_2$ 开始, 用 $Φ_3$ 迭代 $Φ_2$, 得到的函数叫做三元Veblen函数 $\varphi_3 : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- 从 $\varphi_3$ 开始, 用 $Φ_4$ 迭代 $Φ_3$, 得到的函数叫做四元Veblen函数 $\varphi_4 : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- ...

$\varphi_1, \varphi_2, ...$ 分别具有定义

- $\varphi_1 := λα,ω\kern{0.17em}^α$
- $\varphi_2 := Φ_2\kern{0.17em}\varphi_1$
- $\varphi_3 := Φ_3\kern{0.17em}\varphi_2$
- $\varphi_4 := Φ_4\kern{0.17em}\varphi_3$
- ...

剩下的只需要处理 $Φ_2, Φ_3, ...$ 的细节.

下标位是稀缺资源. 后文中, 在没有歧义的情况下, 我们会省去表示元数的下标. 如有歧义, 我们用 $\text{Bin}.Φ, \text{Tri}.Φ, \text{Qua}.Φ,...$ 以及 $\text{Bin}.\varphi, \text{Tri}.\varphi, \text{Qua}.\varphi,...$ 来区分元数. 下文中的下标将另作他用, 注意区分.

## 二元Veblen函数

```agda
module BinaryVeblen where
```

由上面的讨论, 二元版本的 $Φ$ 需要迭代 $\text{fixpt}$, 这也是由强大的 $\text{rec}$ 函数完成的. 注意 $\text{rec}$ 可以处理任意类型 $A$, 一个序数函数类型不管再高阶, 它也是一个类型, 所以适用 $\text{rec}$. 这是类型论语言的方便之处.

**定义** 二元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord}$, 使用 $\text{rec}$, 其三个参数分别如下.

- 初始值: $F$
- 后继步骤: 迭代 $\text{fixpt}$
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作

即

$$
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}\text{fixpt}\kern{0.17em}(λφ,\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]\kern{0.17em}β)
$$

```agda
  Φ : (Ord → Ord) → Ord → Ord → Ord
  Φ F = rec F fixpt (λ φ[_] → jump λ β → lim λ n → φ[ n ] β)
```

**注意** 极限步的跳出操作是反直觉的一步. 从通常的定义式反推不难发现这里需要跳出. 仔细分析二元Veblen函数的序性质才能更好的理解这里跳出的动机, 具体可以参看[Agda大序数(9) 二元Veblen函数](https://zhuanlan.zhihu.com/p/585882648). 这里只需简单的理解为是为了更好的性质和更高的增长率就行了.

**定义** 二元Veblen函数

$$\varphi := Φ\kern{0.17em}λα,ω\kern{0.17em}^α$$

```agda
  φ : Ord → Ord → Ord
  φ = Φ (ω ^_)
```

我们习惯将最后一个参数之前的所有参数都写成下标.

**例** 由定义, 以下等式成立.

$$
\begin{aligned}
\varphi_0 &= λα,ω\kern{0.17em}^α \\
\varphi_1 &= ε \\
\varphi_2 &= ζ \\
\varphi_3 &= η
\end{aligned}
$$

```agda
  φ-0 : φ 0 ≡ ω ^_
  φ-0 = refl

  φ-1 : φ 1 ≡ ε
  φ-1 = refl

  φ-2 : φ 2 ≡ ζ
  φ-2 = refl

  φ-3 : φ 3 ≡ η
  φ-3 = refl
```

**定理** 对于第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+} &= \text{fixpt}\kern{0.17em}φ_α \\
\varphi_{\text{lim}\kern{0.17em}f} &= \text{jump}\kern{0.17em}λα,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}α
\end{aligned}
$$

```agda
  φ-suc : φ (suc α) ≡ fixpt (φ α)
  φ-suc = refl

  φ-lim : φ (lim f) ≡ jump λ α → lim λ n → φ (f n) α
  φ-lim = refl
```

为了对 $\text{jump}$ 的行为有更加直观的感受, 对第一个参数为极限的情况, 我们对第二个参数再次分成零, 后继和极限的情况进行讨论, 有如下等式成立.

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}0 &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(β^+) &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}(\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}β)^+ \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(\text{lim}\kern{0.17em}g) &= \text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f}\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

```agda
  φ-lim-0 : φ (lim f) 0 ≡ lim λ n → φ (f n) 0
  φ-lim-0 = refl

  φ-lim-suc : φ (lim f) (suc β) ≡ lim λ n → φ (f n) (suc (φ (lim f) β))
  φ-lim-suc = refl

  φ-lim-lim : φ (lim f) (lim g) ≡ lim λ n → φ (lim f) (g n)
  φ-lim-lim = refl
```

很快, 我们来到了二元Veblen函数的能力极限.

**定义** 对函数 $λα,φ_α\kern{0.17em}0$ 取不动点枚举, 得到的函数称为 $\Gamma$.

$$
\Gamma := \text{fixpt}\kern{0.17em}λα,φ_α\kern{0.17em}0
$$

```agda
  Γ : Ord → Ord
  Γ = fixpt λ α → φ α 0
```

**例** 最小的 $\Gamma$ 数是

$$Γ_0 := φ_{φ_{φ_{φ_{...}0}\kern{0.17em}0}\kern{0.17em}0}\kern{0.17em}0$$

```agda
  Γ-0 : Γ 0 ≡ iterω (λ α → φ α 0) 0
  Γ-0 = refl
```

没有什么能阻止我们继续取不动点枚举. 将 $\Gamma$ 看作新的 $λα,ω\kern{0.17em}^α$, 我们可以得到所谓第二代 $\varepsilon, \zeta, \eta$ 函数, 分别记作 $\dot{\varepsilon}, \dot{\zeta}, \dot{\eta}$.

$$
\begin{aligned}
\dot{\varepsilon} &:= \text{fixpt}\kern{0.17em}Γ \\
\dot{\zeta} &:= \text{fixpt}\kern{0.17em}\dot{\varepsilon} \\
\dot{\eta} &:= \text{fixpt}\kern{0.17em}\dot{\zeta}
\end{aligned}
$$

```agda
  ε̇ ζ̇ η̇ : Ord → Ord
  ε̇ = fixpt Γ
  ζ̇ = fixpt ε̇
  η̇ = fixpt ζ̇
```

然后有第二代 $\varphi$ 和第二代 $\Gamma$ 函数.

$$
\begin{aligned}
\dot{\varphi} &:= Φ\kern{0.17em}Γ \\
\dot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\dot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

```agda
  φ̇ : Ord → Ord → Ord
  φ̇ = Φ Γ

  Γ̇ : Ord → Ord
  Γ̇ = fixpt λ α → φ̇ α 0
```

乃至第三代 $\varepsilon, \zeta, \eta$ 函数

$$
\begin{aligned}
\ddot{\varepsilon} &:= \text{fixpt}\kern{0.17em}\dot{\Gamma} \\
\ddot{\zeta} &:= \text{fixpt}\kern{0.17em}\ddot{\varepsilon} \\
\ddot{\eta} &:= \text{fixpt}\kern{0.17em}\ddot{\zeta}
\end{aligned}
$$

```agda
  ε̈ ζ̈ η̈ : Ord → Ord
  ε̈ = fixpt Γ̇
  ζ̈ = fixpt ε̈
  η̈ = fixpt ζ̈
```

和第三代 $\varphi$ 和第三代 $\Gamma$ 函数.

$$
\begin{aligned}
\ddot{\varphi} &:= Φ\kern{0.17em}\dot{\Gamma} \\
\ddot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\ddot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

```agda
  φ̈ : Ord → Ord → Ord
  φ̈ = Φ Γ̇

  Γ̈ : Ord → Ord
  Γ̈ = fixpt λ α → φ̈ α 0
```

以此类推, 直至超限代. 三元Veblen函数将把这些后代函数囊括其中.

## 三元Veblen函数

```agda
module TrinaryVeblen where
```

本小节我们将上一小节的谈论过事物 $x$ 记作 $\text{Bin}.x$, 以让出命名空间, 但没有歧义时会省略.

```agda
  private module Bin = BinaryVeblen
  open Bin using (Γ; ε̇; ζ̇; η̇; φ̇; Γ̇; ε̈; ζ̈; η̈; φ̈; Γ̈)
```

**定义** 三元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord} → \text{Ord}$, 使用 $\text{rec}$, 其三个参数分别如下.

- 初始值: $F$
- 后继步骤: 迭代 $λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)$
  - 一些解释
    - 此处迭代的是二元函数 $\text{Ord} → \text{Ord} → \text{Ord}$, 以得到一个三元函数.
    - 参数 $φ_α$ 是上一步的结果, 它是一个二元函数, 看作是对三元函数 $φ$ 输入了上一步的编号 $α$ 所得到的结果.
    - 这一步我们先对 $λβ,φ_{α,β}\kern{0.17em}0$ 取不动点枚举, 再交给二元 $Φ$ 处理
      - 回想上一小节我们是怎么从一代 $φ$ 得到二代 $φ$ 的, 这里的处理方式就是对该操作的反映.
  - 注意: 对任意元 $φ$, 我们都是取第二个参数的不动点枚举, 而对右边剩下的参数全部填零. 二元 $Φ$ 的时候这个规律还看不出来, 现在才显现出来.
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作, 再交给二元 $Φ$ 处理
  - 注意: 与后继步骤类似地, 这里是对第二个参数跳出, 右边其余参数全部填零.

即

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)) \\
&(λφ,\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_β\kern{0.17em}0))
\end{aligned}
$$

```agda
  Φ : (Ord → Ord → Ord) → Ord → Ord → Ord → Ord
  Φ F = rec F
    (λ φ-α  → Bin.Φ $ fixpt λ β → φ-α β 0)
    (λ φ[_] → Bin.Φ $ jump λ β → lim λ n → φ[ n ] β 0)
```

**定义** 三元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Bin}.\varphi$$

```agda
  φ : Ord → Ord → Ord → Ord
  φ = Φ Bin.φ
```

**例** 由定义, 以下等式成立.

$$
\begin{aligned}
\varphi_0 &= \text{Bin}.\varphi \\
\varphi_{1,0} &= \Gamma \\
\varphi_{1,1} &= \dot{\varepsilon} \\
\varphi_{1,2} &= \dot{\zeta} \\
\varphi_{1,3} &= \dot{\eta} \\
\varphi_{1} &= \dot{\varphi} \\
\varphi_{2,0} &= \dot{\Gamma} \\
\varphi_{2,1} &= \ddot{\varepsilon} \\
\varphi_{2,2} &= \ddot{\zeta} \\
\varphi_{2,3} &= \ddot{\eta} \\
\varphi_{2} &= \ddot{\varphi} \\
\varphi_{3,0} &= \ddot{\Gamma} \\
\end{aligned}
$$

```agda
  φ-0 : φ 0 ≡ Bin.φ
  φ-0 = refl

  φ-1-0 : φ 1 0 ≡ Γ
  φ-1-0 = refl

  φ-1-1 : φ 1 1 ≡ ε̇
  φ-1-1 = refl

  φ-1-2 : φ 1 2 ≡ ζ̇
  φ-1-2 = refl

  φ-1-3 : φ 1 3 ≡ η̇
  φ-1-3 = refl

  φ-1 : φ 1 ≡ φ̇
  φ-1 = refl

  φ-2-0 : φ 2 0 ≡ Γ̇
  φ-2-0 = refl

  φ-2-1 : φ 2 1 ≡ ε̈
  φ-2-1 = refl

  φ-2-2 : φ 2 2 ≡ ζ̈
  φ-2-2 = refl

  φ-2-3 : φ 2 3 ≡ η̈
  φ-2-3 = refl

  φ-2 : φ 2 ≡ φ̈
  φ-2 = refl

  φ-3-0 : φ 3 0 ≡ Γ̈
  φ-3-0 = refl
```

**定理** 对于第一个参数为后继的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0} &= \text{fixpt}λβ,φ_{α,β}\kern{0.17em}0 \\
\varphi_{α^+,β^+} &= \text{fixpt}\kern{0.17em}φ_{α^+,β} \\
\varphi_{α^+,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α^+,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

```agda
  φ-suc-0 : φ (suc α) 0 ≡ fixpt λ β → φ α β 0
  φ-suc-0 = refl

  φ-suc-suc : φ (suc α) (suc β) ≡ fixpt (φ (suc α) β)
  φ-suc-suc = refl

  φ-suc-lim : φ (suc α) (lim g) ≡ jump λ γ → lim λ n → φ (suc α) (g n) γ
  φ-suc-lim = refl
```

**定理** 对于第一个参数为极限的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,β^+} &= \text{fixpt}\kern{0.17em}φ_{\text{lim}\kern{0.17em}f,β}\kern{0.17em} \\
\varphi_{\text{lim}\kern{0.17em}f,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

```agda
  φ-lim-0 : φ (lim f) 0 ≡ jump λ β → lim λ n → φ (f n) β 0
  φ-lim-0 = refl

  φ-lim-suc : φ (lim f) (suc β) ≡ fixpt (φ (lim f) β)
  φ-lim-suc = refl

  φ-lim-lim : φ (lim f) (lim g) ≡ jump λ γ → lim λ n → φ (lim f) (g n) γ
  φ-lim-lim = refl
```

## 四元Veblen函数

```agda
module QuaternaryVeblen where
  private module Bin = BinaryVeblen
  private module Tri = TrinaryVeblen
```

摸清二元到三元的规律之后, 三元到四元就是按部就班的操作了.

**定义** 四元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$, 使用 $\text{rec}$

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0))) \\
&(λφ,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_{β,0}\kern{0.17em}0)))
\end{aligned}
$$

```agda
  Φ : (Ord → Ord → Ord → Ord) → (Ord → Ord → Ord → Ord → Ord)
  Φ F = rec F
    (λ φ-α  → Tri.Φ $ Bin.Φ $ fixpt λ β → φ-α β 0 0)
    (λ φ[_] → Tri.Φ $ Bin.Φ $ jump λ β → lim λ n → φ[ n ] β 0 0)
```

**定义** 四元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Tri}.\varphi$$

```agda
  φ : Ord → Ord → Ord → Ord → Ord
  φ = Φ Tri.φ
```

**例** 第一个参数从无效到刚开始生效, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_0 &= \text{Tri}.\varphi \\
\varphi_{1,0,0} &= \text{fixpt}\kern{0.17em}λα,\text{Tri}.\varphi_{α,0}\kern{0.17em}0 \\
\end{aligned}
$$

```agda
  φ-0 : φ 0 ≡ Tri.φ
  φ-0 = refl

  φ-1-0-0 : φ 1 0 0 ≡ fixpt (λ α → Tri.φ α 0 0)
  φ-1-0-0 = refl
```

**定理** 中间两个参数为零, 讨论第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0,0} &= \text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,0,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β,0}\kern{0.17em}0
\end{aligned}
$$

```agda
  φ-suc-0-0 : φ (suc α) 0 0 ≡ fixpt λ β → φ α β 0 0
  φ-suc-0-0 = refl

  φ-lim-0-0 : φ (lim f) 0 0 ≡ jump λ β → lim λ n → φ (f n) β 0 0
  φ-lim-0-0 = refl
```

**定理** 将 $φ_α$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β^+,0} &= \text{fixpt}\kern{0.17em}λγ,φ_{α,β,γ}\kern{0.17em}0 \\
\varphi_{α,\text{lim}\kern{0.17em}g,0} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α,g\kern{0.17em}n,γ}\kern{0.17em}0
\end{aligned}
$$

```agda
  φ-α-suc-0 : φ α (suc β) 0 ≡ fixpt λ γ → φ α β γ 0
  φ-α-suc-0 {α = zero}  = refl
  φ-α-suc-0 {α = suc _} = refl
  φ-α-suc-0 {α = lim f} = refl

  φ-α-lim-0 : φ α (lim g) 0 ≡ jump λ γ → lim λ n → φ α (g n) γ 0
  φ-α-lim-0 {α = zero}  = refl
  φ-α-lim-0 {α = suc _} = refl
  φ-α-lim-0 {α = lim f} = refl
```

**定理** 将 $φ_{α,β}$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β,γ^+} &= \text{fixpt}\kern{0.17em}φ_{α,β,γ} \\
\varphi_{α,β,\text{lim}\kern{0.17em}h} &= \text{jump}\kern{0.17em}λδ,\text{lim}\kern{0.17em}λn,φ_{α,β,h\kern{0.17em}n}\kern{0.17em}δ
\end{aligned}
$$

```agda
  φ-α-β-suc : φ α β (suc γ) ≡ fixpt (φ α β γ)
  φ-α-β-suc {α = zero}  {β = zero}  = refl
  φ-α-β-suc {α = zero}  {β = suc _} = refl
  φ-α-β-suc {α = zero}  {β = lim _} = refl
  φ-α-β-suc {α = suc _} {β = zero}  = refl
  φ-α-β-suc {α = suc _} {β = suc _} = refl
  φ-α-β-suc {α = suc _} {β = lim _} = refl
  φ-α-β-suc {α = lim _} {β = zero}  = refl
  φ-α-β-suc {α = lim _} {β = suc _} = refl
  φ-α-β-suc {α = lim _} {β = lim _} = refl

  φ-α-β-lim : φ α β (lim h) ≡ jump λ δ → lim λ n → φ α β (h n) δ
  φ-α-β-lim {α = zero}  {β = zero}  = refl
  φ-α-β-lim {α = zero}  {β = suc _} = refl
  φ-α-β-lim {α = zero}  {β = lim _} = refl
  φ-α-β-lim {α = suc _} {β = zero}  = refl
  φ-α-β-lim {α = suc _} {β = suc _} = refl
  φ-α-β-lim {α = suc _} {β = lim _} = refl
  φ-α-β-lim {α = lim _} {β = zero}  = refl
  φ-α-β-lim {α = lim _} {β = suc _} = refl
  φ-α-β-lim {α = lim _} {β = lim _} = refl
```

**例** 一个很大的大数:

$$
\text{oom}_2 := f_{φ_{Γ_0,0,0}\kern{0.17em}(0)}(99)
$$

```agda
oom₂ = FGH.f (QuaternaryVeblen.φ (BinaryVeblen.Γ 0) 0 0 0) 99
```
