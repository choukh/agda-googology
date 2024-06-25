---
title: 形式化大数数学 (1.2 - Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.2 - Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Multinary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Multinary.lagda.md)  
> 高亮渲染: [Multinary.html](https://choukh.github.io/agda-googology/Veblen.Multinary.html)  

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

下标位是稀缺资源. 后文中, 在没有歧义的情况下, 我们会省去表示元数的下标. 如有歧义, 我们用 $\text{Bin}.Φ, \text{Tri}.Φ, \text{Qua}.Φ,...$ 以及 $\text{Bin}.\varphi, \text{Tri}.\varphi, \text{Qua}.\varphi,...$ 来区分元数. 下文中出现的 $\varphi_1, \varphi_2,...$ 将指代别的东西.

## 二元Veblen函数

```agda
module BinaryVeblen where
```

由上面的讨论, 二元版本的 $Φ$ 需要迭代 $\text{fixpt}$, 这也是由强大的 $\text{rec}$ 函数完成的. 注意 $\text{rec}$ 可以处理任意类型 $A$, 一个序数函数类型不管再高阶, 它也是一个类型, 所以适用 $\text{rec}$. 这是类型论语言的方便之处.

**定义** 二元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord}$, 使用 $\text{rec}$, 按以下参数递归.
- 起始步骤: $F$
- 递归步骤: 迭代 $\text{fixpt}$
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作

$$
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}\text{fixpt}\kern{0.17em}F\kern{0.17em}(λφ,\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]\kern{0.17em}β)
$$

```agda
  Φ : (Ord → Ord) → Ord → Ord → Ord
  Φ F = rec F fixpt (λ φ[_] → jump λ β → lim λ n → φ[ n ] β)
```

**注意** 极限步的跳出操作是反直觉的一步. 从通常的定义式反推不难发现这里需要跳出. 仔细分析二元Veblen函数的序性质才能更好的理解这里跳出的动机, 具体可以参看[Agda大序数(9) 二元Veblen函数](https://zhuanlan.zhihu.com/p/585882648). 这里只需简单的理解为是为了更好的性质和更高的增长率就行了.

**定义** 二元Veblen函数 $\varphi$ 为 $Φ\kern{0.17em}(λα,ω\kern{0.17em}^α)$.

```agda
  φ : Ord → Ord → Ord
  φ = Φ (ω ^_)
```

**例** 由定义, 以下等式成立.

$$
\begin{aligned}
\varphi\kern{0.17em}0 &≡ λα,ω\kern{0.17em}^α \\
\varphi\kern{0.17em}1 &≡ ε \\
\varphi\kern{0.17em}2 &≡ ζ \\
\varphi\kern{0.17em}3 &≡ η
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

```agda
  φ-suc : φ (suc α) ≡ fixpt (φ α)
  φ-suc = refl
```

```agda
  φ-lim : φ (lim f) ≡ jump λ α → lim λ n → φ (f n) α
  φ-lim = refl
```

```agda
  φ-lim-0 : φ (lim f) 0 ≡ lim λ n → φ (f n) 0
  φ-lim-0 = refl
```

```agda
  φ-lim-suc : φ (lim f) (suc α) ≡ lim λ n → φ (f n) (suc (φ (lim f) α))
  φ-lim-suc = refl
```

```agda
  φ-lim-lim : φ (lim f) (lim g) ≡ lim λ n → φ (lim f) (g n)
  φ-lim-lim = refl
```

```agda
  Γ : Ord → Ord
  Γ = fixpt λ α → φ α 0
```

```agda
  Γ-0 : Γ 0 ≡ iterω (λ α → φ α 0) 0
  Γ-0 = refl
```

```agda
  ε₁ ζ₁ η₁ : Ord → Ord
  ε₁ = fixpt Γ
  ζ₁ = fixpt ε₁
  η₁ = fixpt ζ₁
```

```agda
  φ₁ : Ord → Ord → Ord
  φ₁ = Φ Γ

  Γ₁ : Ord → Ord
  Γ₁ = fixpt λ α → φ₁ α 0
```

```agda
  ε₂ ζ₂ η₂ : Ord → Ord
  ε₂ = fixpt Γ₁
  ζ₂ = fixpt ε₂
  η₂ = fixpt ζ₂
```

```agda
  φ₂ : Ord → Ord → Ord
  φ₂ = Φ Γ₁

  Γ₂ : Ord → Ord
  Γ₂ = fixpt λ α → φ₂ α 0
```

## 三元Veblen函数

```agda
module TrinaryVeblen where
  private module Bin = BinaryVeblen

  Φ : (Ord → Ord → Ord) → Ord → Ord → Ord → Ord
  Φ F = rec F
    (λ φ-α  → Bin.Φ $ fixpt λ β → φ-α β 0)
    (λ φ[_] → Bin.Φ $ jump λ β → lim λ n → φ[ n ] β 0)
```

```agda
  φ : Ord → Ord → Ord → Ord
  φ = Φ Bin.φ
```

```agda
  φ-0 : φ 0 ≡ Bin.φ
  φ-0 = refl
```

```agda
  φ-suc-0 : φ (suc α) 0 ≡ fixpt λ β → φ α β 0
  φ-suc-0 = refl
```

```agda
  φ-suc-suc : φ (suc α) (suc β) ≡ fixpt (φ (suc α) β)
  φ-suc-suc = refl
```

```agda
  φ-suc-lim : φ (suc α) (lim g) ≡ jump λ γ → lim λ n → φ (suc α) (g n) γ
  φ-suc-lim = refl
```

```agda
  φ-lim-0 : φ (lim f) 0 ≡ jump λ β → lim λ n → φ (f n) β 0
  φ-lim-0 = refl
```

```agda
  φ-lim-suc : φ (lim f) (suc β) ≡ fixpt (φ (lim f) β)
  φ-lim-suc = refl
```

```agda
  φ-lim-lim : φ (lim f) (lim g) ≡ jump λ γ → lim λ n → φ (lim f) (g n) γ
  φ-lim-lim = refl
```

```agda
  φ-1-0 : φ 1 0 ≡ Bin.Γ
  φ-1-0 = refl
```

```agda
  φ-1-1 : φ 1 1 ≡ Bin.ε₁
  φ-1-1 = refl
```

```agda
  φ-1-2 : φ 1 2 ≡ Bin.ζ₁
  φ-1-2 = refl
```

```agda
  φ-1-3 : φ 1 3 ≡ Bin.η₁
  φ-1-3 = refl
```

```agda
  φ-1 : φ 1 ≡ Bin.φ₁
  φ-1 = refl
```

```agda
  φ-2-0 : φ 2 0 ≡ Bin.Γ₁
  φ-2-0 = refl
```

```agda
  φ-2-1 : φ 2 1 ≡ Bin.ε₂
  φ-2-1 = refl
```

```agda
  φ-2-2 : φ 2 2 ≡ Bin.ζ₂
  φ-2-2 = refl
```

```agda
  φ-2-3 : φ 2 3 ≡ Bin.η₂
  φ-2-3 = refl
```

```agda
  φ-2 : φ 2 ≡ Bin.φ₂
  φ-2 = refl
```

```agda
  φ-3-0 : φ 3 0 ≡ Bin.Γ₂
  φ-3-0 = refl
```

## 四元Veblen函数

```agda
module QuaternaryVeblen where
  private module Bin = BinaryVeblen
  private module Tri = TrinaryVeblen

  Φ : (Ord → Ord → Ord → Ord) → (Ord → Ord → Ord → Ord → Ord)
  Φ F = rec F
    (λ φ-α  → Tri.Φ $ Bin.Φ $ fixpt λ β → φ-α β 0 0)
    (λ φ[_] → Tri.Φ $ Bin.Φ $ jump λ β → lim λ n → φ[ n ] β 0 0)
```

```agda
  φ : Ord → Ord → Ord → Ord → Ord
  φ = Φ Tri.φ
```

```agda
  φ-0 : φ 0 ≡ Tri.φ
  φ-0 = refl
```

```agda
  φ-1-0-0 : φ 1 0 0 ≡ fixpt (λ α → Tri.φ α 0 0)
  φ-1-0-0 = refl
```

```agda
  φ-suc-0-0 : φ (suc α) 0 0 ≡ fixpt λ β → φ α β 0 0
  φ-suc-0-0 = refl
```

```agda
  φ-lim-0-0 : φ (lim f) 0 0 ≡ jump λ β → lim λ n → φ (f n) β 0 0
  φ-lim-0-0 = refl
```

```agda
  φ-α-suc-0 : φ α (suc β) 0 ≡ fixpt λ γ → φ α β γ 0
  φ-α-suc-0 {α = zero}  = refl
  φ-α-suc-0 {α = suc _} = refl
  φ-α-suc-0 {α = lim f} = refl
```

```agda
  φ-α-lim-0 : φ α (lim g) 0 ≡ jump λ γ → lim λ n → φ α (g n) γ 0
  φ-α-lim-0 {α = zero}  = refl
  φ-α-lim-0 {α = suc _} = refl
  φ-α-lim-0 {α = lim f} = refl
```

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
```

```agda
  φ-α-β-lim : φ α β (lim g) ≡ jump λ γ → lim λ n → φ α β (g n) γ
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
