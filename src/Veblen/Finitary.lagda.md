---
title: 形式化大数数学 (1.3 - 有限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.3 - 有限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Finitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Finitary.lagda.md)  
> 高亮渲染: [Finitary.html](https://choukh.github.io/agda-googology/Veblen.Finitary.html)  

```agda
{-# OPTIONS --lossy-unification #-}

module Veblen.Finitary where
open import Veblen.Multinary public
module Bin = BinaryVeblen
module Tri = TrinaryVeblen
module Qua = QuaternaryVeblen
```

前篇我们讲了二元, 三元和四元Veblen函数 $\text{Bin}.φ,\text{Tri}.φ,\text{Qua}.φ$. 我们希望把元数作为一个参数, 也就是说, 定义一个函数族 $φ$, 使得 $φ_n$ 正好是 $n$ 元Veblen函数. 这样的 $φ$ 叫做 (任意) 有限元Veblen函数 (Finitary Veblen Function), 也叫扩展Veblen函数 (Extended Veblen Function).

## 有限元函数类型

首先我们要把 $φ$ 的类型写出来, 它是一个依赖类型 $\Pi_{n:ℕ}\text{Ord}^{→n}$, 其中 $\text{Ord}^{→n}$ 表示 $\text{Ord}$ 上的 $n$ 元函数类型 $\overbrace{\text{Ord}→...→\text{Ord}}^n →\text{Ord}$. 当然我们也可以采用 $\text{Ord}^n →\text{Ord}$, 即 ($\overbrace{\text{Ord}\times...\times\text{Ord}}^n)→\text{Ord}$. 我们选择前者是因为它有方便的[柯里化 (Currying)](https://en.wikipedia.org/wiki/Currying) 性质, 处理起来更简单.

**定义** 陪域为 $A$ 的有限元序数函数 $\overbrace{\text{Ord}→...→\text{Ord}}^n →A$, 记作 $A^{→n}$, 递归定义为

$$
\begin{aligned}
A^{→0} &= A \\
A^{→n^+} &= \text{Ord} → A^{→n}
\end{aligned}
$$

```agda
_→ⁿ_ : Set → ℕ → Set
A →ⁿ zero = A
A →ⁿ suc n = Ord → A →ⁿ n
```

这样, $\text{Ord}^{→n}$ 就等于 $\overbrace{\text{Ord}→...→\text{Ord}}^n →\text{Ord}$.

现在, 回想四元Veblen函数的定义

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0))) \\
&(λφ,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_{β,0}\kern{0.17em}0)))
\end{aligned}
$$

注意其中 $φ_{α,β,0}\kern{0.17em}0$ 的形式, 也就是说我们需要从某一位参数开始, 后面全部填零的操作. 对于 $n$ 元函数来说这种填零操作是递归完成的. 于是有如下定义.

**定义** 对函数 $F : A^{→n}$ 的参数全部填零所得到的 $A$ 的元素, 记作 $F\kern{0.17em}0⋯0 : A$, 递归定义为

$$
\begin{aligned}
(F : A^{→0})\kern{0.17em}0⋯0 &= F:A \\
(F : A^{→n^+})\kern{0.17em}0⋯0 &= (F\kern{0.17em}0 : A^{→n})\kern{0.17em}0⋯0
\end{aligned}
$$

```agda
_0⋯0 : A →ⁿ n → A
_0⋯0 {n = zero} = id
_0⋯0 {n = suc n} F = F 0 0⋯0
```

有时候我们想要留最后一位不填或最后两位不填.

**定义** 对函数 $F : A^{→n^+}$ 的参数留最后一位不填, 其余全部填零, 所得到的函数 $\text{Ord}→A$, 记作 $F\kern{0.17em}0⋯\_$, 递归定义为

$$
\begin{aligned}
(F : A^{→1})\kern{0.17em}0⋯\_ &= F:\text{Ord}→A \\
(F : A^{→n^{++}})\kern{0.17em}0⋯\_ &= (F\kern{0.17em}0 : A^{→n^+})\kern{0.17em}0⋯\_
\end{aligned}
$$

```agda
_0⋯_ : A →ⁿ (suc n) → A →ⁿ 1
_0⋯_ {n = zero} = id
_0⋯_ {n = suc n} F = F 0 0⋯_
```

**定义** 对函数 $F : A^{→n^{++}}$ 的参数留最后两位不填, 其余全部填零, 所得到的函数 $\text{Ord}→\text{Ord}→A$, 记作 $F\kern{0.17em}0⋯\_,\_$, 递归定义为

$$
\begin{aligned}
(F : A^{→2})\kern{0.17em}0⋯\_,\_ &= F:\text{Ord}→\text{Ord}→A \\
(F : A^{→n^{+++}})\kern{0.17em}0⋯\_,\_ &= (F\kern{0.17em}0 : A^{→n^{++}})\kern{0.17em}0⋯\_,\_
\end{aligned}
$$

```agda
_0⋯_,_ : A →ⁿ (2+ n) → A →ⁿ 2
_0⋯_,_ {n = zero} = id
_0⋯_,_ {n = suc n} F = F 0 0⋯_,_
```

**引理** 对 $n$ 元函数 $F : A^{→n^+}$, 第一位先填零, 剩余再全部填零, 或者除最后一位外全部填零, 然后最后一位再填零, 这两种做法都等于一开始就全部填零.

$$
\begin{aligned}
F\kern{0.17em}0⋯0 &= F\kern{0.17em}0\kern{0.17em}0⋯0 \\
F\kern{0.17em}0⋯0 &= F\kern{0.17em}0⋯\underbar{0}
\end{aligned}
$$

```agda
0-0⋯ : {F : A →ⁿ (suc n)} → F 0⋯0 ≡ F 0 0⋯0
0-0⋯ = refl

⋯0-0 : {F : A →ⁿ (suc n)} → F 0⋯0 ≡ F 0⋯ 0
⋯0-0 {n = zero} = refl
⋯0-0 {n = suc _} {F} = ⋯0-0 {F = F 0}
```

## 有限元Veblen函数

有了以上准备, 终于可以定义有限元Veblen函数了.

**定义**

```agda
Φ : Ord →ⁿ suc n → Ord →ⁿ 2+ n
Φⁿ : (Ord → Ord) → Ord →ⁿ suc n
```

```agda
Φ F = rec F
  (λ φ-α  → Φⁿ $ fixpt λ β → φ-α β 0⋯0)
  (λ φ[_] → Φⁿ $ jump λ β → lim λ n → φ[ n ] β 0⋯0)
```

```agda
Φⁿ {n = zero} = id
Φⁿ {n = suc n} F = Φ (Φⁿ F)
```

**定义**

```agda
φ : Ord →ⁿ suc n
φ = Φⁿ (ω ^_)
```

**事实**

```agda
Φ-φ : φ {suc n} ≡ Φ (φ {n})
Φ-φ = refl
```

**事实**

```agda
φ-0 : φ {suc n} 0 ≡ φ {n}
φ-0 = refl
```

**例**

```agda
φ₀ : φ {0} ≡ ω ^_
φ₀ = refl
```

```agda
φ₁ : φ {1} ≡ Bin.φ
φ₁ = refl
```

```agda
φ₂ : φ {2} ≡ Tri.φ
φ₂ = refl
```

```agda
φ₃ : φ {3} ≡ Qua.φ
φ₃ = refl
```

**引理**

```agda
Φⁿ-0⋯x : Φⁿ {n} F 0⋯_ ≡ F
Φⁿ-0⋯x {n = zero} = refl
Φⁿ-0⋯x {n = suc n} = Φⁿ-0⋯x {n}
```

**定理**

```agda
φ-s-z⋯x : φ {suc n} (suc α) 0⋯_ ≡ fixpt λ β → φ α β 0⋯0
φ-s-z⋯x {n} {α} = begin
  φ {suc n} (suc α) 0⋯_           ≡⟨⟩
  Φ (φ {n}) (suc α) 0⋯_           ≡⟨⟩
  Φⁿ (fixpt λ β → φ α β 0⋯0) 0⋯_  ≡⟨ Φⁿ-0⋯x ⟩
  fixpt (λ β → φ α β 0⋯0)         ∎
```

**定理**

```agda
φ-l-z⋯x : φ {suc n} (lim f) 0⋯_ ≡ jump λ β → lim λ m → φ {suc n} (f m) β 0⋯0
φ-l-z⋯x {n} {f} = begin
  φ {suc n} (lim f) 0⋯_                       ≡⟨⟩
  Φ (φ {n}) (lim f) 0⋯_                       ≡⟨⟩
  Φⁿ (jump λ β → lim λ m → φ (f m) β 0⋯0) 0⋯_ ≡⟨ Φⁿ-0⋯x ⟩
  jump (λ β → lim λ m → φ (f m) β 0⋯0)        ∎
```

回想二元Veblen函数的计算式

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}0 &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(β^+) &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}(\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}β)^+ \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(\text{lim}\kern{0.17em}g) &= \text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f}\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

**推论**

```agda
φ-l-z⋯z : φ {n} (lim f) 0⋯0 ≡ lim λ m → φ {n} (f m) 0⋯0
φ-l-z⋯z {n = zero} = refl
φ-l-z⋯z {n = suc n} {f} = begin
  φ {suc n} (lim f) 0 0⋯0                         ≡⟨ ⋯0-0 ⟩
  φ {suc n} (lim f) 0⋯ 0                          ≡⟨ cong-app φ-l-z⋯x 0 ⟩
  jump (λ β → lim λ m → φ {suc n} (f m) β 0⋯0) 0  ≡⟨⟩
  lim (λ m → φ (f m) 0⋯0)                         ∎
```

```agda
φ-l-z⋯s : φ {suc n} (lim f) 0⋯ (suc α) ≡ lim λ m → φ (f m) (suc (φ {suc n} (lim f) 0⋯ α)) 0⋯0
φ-l-z⋯s {n} {f} {α} =
  let j = jump λ β → lim λ m → φ (f m) β 0⋯0 in   begin
  φ {suc n} (lim f) 0⋯ (suc α)                    ≡⟨ cong-app φ-l-z⋯x (suc α) ⟩
  j (suc α)                                       ≡⟨⟩
  lim (λ m → φ (f m) (suc (j α)) 0⋯0)             ≡˘⟨
    cong (λ x → lim (λ m → φ {suc n} (f m) (suc (x α)) 0⋯0)) φ-l-z⋯x ⟩
  lim (λ m → φ (f m) (suc (φ (lim f) 0⋯ α)) 0⋯0)  ∎
```

```agda
φ-l-z⋯l : φ {suc n} (lim f) 0⋯ (lim g) ≡ lim λ m → φ (lim f) 0⋯ (g m)
φ-l-z⋯l {n} {f} {g} =
  let j = jump λ β → lim λ m → φ (f m) β 0⋯0 in begin
  φ {suc n} (lim f) 0⋯ (lim g)                  ≡⟨ cong-app φ-l-z⋯x (lim g) ⟩
  j (lim g)                                     ≡⟨⟩
  lim (λ m → j (g m))                           ≡˘⟨ cong (λ x → lim (λ m → x (g m))) φ-l-z⋯x ⟩
  lim (λ m → φ (lim f) 0⋯ (g m))                ∎
```

**定理**

```agda
φ-x-s-0⋯y : φ {2+ n} α (suc β) 0⋯_ ≡ fixpt λ γ → φ {2+ n} α β γ 0⋯0
φ-x-s-0⋯y {n = zero} {α = zero} = refl
φ-x-s-0⋯y {n = zero} {α = suc _} = refl
φ-x-s-0⋯y {n = zero} {α = lim _} = refl
φ-x-s-0⋯y {n = suc n} {α = zero} = Φⁿ-0⋯x
φ-x-s-0⋯y {n = suc n} {α = suc _} = Φⁿ-0⋯x
φ-x-s-0⋯y {n = suc n} {α = lim _} = Φⁿ-0⋯x

φ-x-l-0⋯y : φ {2+ n} α (lim f) 0⋯_ ≡ jump λ δ → lim λ m → φ {2+ n} α (f m) δ 0⋯0
φ-x-l-0⋯y {n = zero} {α = zero} = refl
φ-x-l-0⋯y {n = zero} {α = suc _} = refl
φ-x-l-0⋯y {n = zero} {α = lim _} = refl
φ-x-l-0⋯y {n = suc n} {α = zero} = Φⁿ-0⋯x
φ-x-l-0⋯y {n = suc n} {α = suc _} = Φⁿ-0⋯x
φ-x-l-0⋯y {n = suc n} {α = lim _} = Φⁿ-0⋯x
```

**引理**

```agda
Φ-0⋯s-x : Φ {n} (Φⁿ F) 0⋯ (suc α) ,_ ≡ fixpt (Φ {n} (Φⁿ F) 0⋯ α ,_)
Φ-0⋯s-x {n = zero} = refl
Φ-0⋯s-x {n = suc n} = Φ-0⋯s-x {n}

Φ-0⋯l-x : Φ {n} (Φⁿ F) 0⋯ (lim f) ,_ ≡ jump λ β → lim λ m → Φ {n} (Φⁿ F) 0⋯ (f m) , β
Φ-0⋯l-x {n = zero} = refl
Φ-0⋯l-x {n = suc n} = Φ-0⋯l-x {n}
```

**定理**

```agda
φ-0⋯s-x : φ {suc n} 0⋯ (suc α) ,_ ≡ fixpt (φ {suc n} 0⋯ α ,_)
φ-0⋯s-x = Φ-0⋯s-x

φ-0⋯l-x : φ {suc n} 0⋯ (lim f) ,_ ≡ jump λ β → lim λ m → φ {suc n} 0⋯ (f m) , β
φ-0⋯l-x = Φ-0⋯l-x
```

**定理**

```agda
φ-x-0⋯s-y : φ {2+ n} α 0⋯ (suc β) ,_ ≡ fixpt (φ {2+ n} α 0⋯ β ,_)
φ-x-0⋯s-y {n = zero} {α = zero} = refl
φ-x-0⋯s-y {n = zero} {α = suc _} = refl
φ-x-0⋯s-y {n = zero} {α = lim _} = refl
φ-x-0⋯s-y {n = suc n} {α = zero} = Φ-0⋯s-x
φ-x-0⋯s-y {n = suc n} {α = suc _} = Φ-0⋯s-x
φ-x-0⋯s-y {n = suc n} {α = lim _} = Φ-0⋯s-x

φ-x-0⋯l-y : φ {2+ n} α 0⋯ (lim f) ,_ ≡ jump λ δ → lim λ m → φ {2+ n} α 0⋯ (f m) , δ
φ-x-0⋯l-y {n = zero} {α = zero} = refl
φ-x-0⋯l-y {n = zero} {α = suc _} = refl
φ-x-0⋯l-y {n = zero} {α = lim _} = refl
φ-x-0⋯l-y {n = suc n} {α = zero} = Φ-0⋯l-x
φ-x-0⋯l-y {n = suc n} {α = suc _} = Φ-0⋯l-x
φ-x-0⋯l-y {n = suc n} {α = lim _} = Φ-0⋯l-x
```

## SVO

**定义**

SVO (~~Subject–Verb–Object~~ Small Veblen Ordinal)

```agda
SVO : Ord
SVO = lim λ n → φ {n} 1 0⋯0
```

一个很大的大数:

```agda
svo₉₉ = FGH.f SVO 99
```
