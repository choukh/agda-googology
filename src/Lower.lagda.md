---
title: 形式化大数数学 (0.0 - 高德纳箭头, 康威链箭)
zhihu-tags: Agda, 大数数学
---

# 形式化大数数学 (0.0 - 高德纳箭头, 康威链箭)

> 交流Q群: 893531731  
> 本文源码: [Lower.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Lower.lagda.md)  
> 高亮渲染: [Lower.html](https://choukh.github.io/agda-googology/Lower.html)  

```agda
{-# OPTIONS --safe #-}
module Lower where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

本篇是[形式化大数数学 (1.0 - 序数, 增长层级, 不动点)](https://zhuanlan.zhihu.com/p/705306447)的前传, 我们快速介绍一些比较弱的著名大数记号, 这部分是入门的入门. 首先要理解的是各种大数记号的核心思想——迭代.

## 迭代

我们知道自然数类型 $ℕ$ 由如下两条规则定义.

$$
\frac{}{\kern{0.17em}\text{zero} : ℕ\kern{0.17em}}
\qquad
\frac{\alpha:ℕ}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:ℕ\kern{0.17em}}
$$

```agda
open import Data.Nat using (ℕ; zero; suc)
```

**约定** 我们用 $A$ 表示任意类型.

```agda
variable A : Set
```

**定义** 函数 $F : A → A$ 的 $n$ 次复合叫做 $F$ 的 $n$ 次迭代, 记作 $F^n$

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{n^+} &= F \circ F^n
\end{aligned}
$$

其中 $\text{id}$ 是恒等函数, 就是输入什么返回什么.

```agda
open import Function public using (id; _∘_)

_∘ⁿ_ : (A → A) → ℕ → (A → A)
F ∘ⁿ zero  = id
F ∘ⁿ suc n = F ∘ (F ∘ⁿ n)
```

## 自然数算术

**定义** 从 $m$ 开始做 $n$ 次后继叫做自然数加法, 记作 $m+n$

$$
m + n := \text{suc}^n\kern{0.17em}m
$$

```agda
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + n = (suc ∘ⁿ n) m
```

**定义** 从 $0$ 开始做 $n$ 次 $+ m$ 叫做自然数乘法, 记作 $m×n$, 简记作 $mn$

$$
m × n := (+m)^n\kern{0.17em}0
$$

```agda
infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
m * n = ((_+ m) ∘ⁿ n) 0
```

**定义** 从 $1$ 开始做 $n$ 次 $× m$ 叫做自然数幂运算, 也叫乘方, 记作 $m^n$

$$
m^n := (×m)^n\kern{0.17em}1
$$

```agda
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
m ^ n = ((_* m) ∘ⁿ n) 1
```

**例**

$$
2^5 = 32 \\
3^5 = 243
$$

```agda
_ : 2 ^ 5 ≡ 32
_ = refl

_ : 3 ^ 5 ≡ 243
_ = refl
```

## 阿克曼函数

阿克曼函数是最简单和最早发现的非原始递归的可计算全函数. 它有很多版本, 常见的双参数版本定义如下.

**定义** 双参数阿克曼函数 $\text{Ack}\kern{0.17em}m\kern{0.17em}n$

$$
\begin{aligned}
\text{Ack}\kern{0.17em}0 &:= \text{suc} \\
\text{Ack}\kern{0.17em}m^+\kern{0.17em}n&:= (\text{Ack}\kern{0.17em}m)^n\kern{0.17em}(\text{Ack}\kern{0.17em}m\kern{0.17em}1)
\end{aligned}
$$

```agda
Ack : ℕ → ℕ → ℕ
Ack zero = suc
Ack (suc m) n = (Ack m ∘ⁿ n) (Ack m 1)
```

### 数值表

![阿克曼函数数值表](https://pic4.zhimg.com/80/v2-e37f9128a7d99a3e31001d403fa26001.png)

```agda
_ : Ack 0 4 ≡ 5
_ = refl

_ : Ack 1 4 ≡ 6
_ = refl

_ : Ack 2 4 ≡ 11
_ = refl

_ : Ack 3 4 ≡ 125
_ = refl
```

从表中第 $n$ 列的形式可以看到 $\text{Ack}\kern{0.17em}m$ 大致具有第 $m$ 级运算的增长率. 其中的高德纳箭头 $↑$ 和康威链箭 $→$ 介绍如下.

## 高德纳箭头

高德纳箭头是「将乘方看作乘法的迭代」这一思想的推广. 零个箭头是加法的迭代 (乘法), 一个箭头是乘法的迭代 (乘方), 两个箭头是一个箭头的迭代, 以此类推.

**定义** 高德纳箭头有三个参数, 左右两边是底数和指数, 中间是箭头的数量.

$$
\begin{aligned}
m ↑^0 n &:= mn \\
m ↑^{k^+} 0 &:= 1 \\
m ↑^{k^+} n^+ &:= (m ↑^k)^n\kern{0.17em}m
\end{aligned}
$$

```agda
infixr 9 _↑⟨_⟩_
_↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
m ↑⟨ zero ⟩ n = m * n
m ↑⟨ suc k ⟩ 0 = 1
m ↑⟨ suc k ⟩ suc n = ((m ↑⟨ k ⟩_) ∘ⁿ n) m
```

**例**

$$
\begin{aligned}
2 ↑^0 3 &= 2×3 &=& 2 + 2 + 2 \\
2 ↑^1 3 &= 2^3 &=& 2 × 2 × 2 \\
2 ↑^2 3 &= {^3}2 &=& 2 ^ {2 ^ 2} \\
2 ↑^3 3 &&=& 2 ↑^2 2 ↑^2 2
\end{aligned}
$$

```agda
_ : 2 ↑⟨ 0 ⟩ 3 ≡ 2 + 2 + 2
_ = refl

_ : 2 ↑⟨ 1 ⟩ 3 ≡ 2 * 2 * 2
_ = refl

_ : 2 ↑⟨ 2 ⟩ 3 ≡ 2 ^ 2 ^ 2
_ = refl

_ : 2 ↑⟨ 3 ⟩ 3 ≡ 2 ↑⟨ 2 ⟩ 2 ↑⟨ 2 ⟩ 2
_ = refl
```

## 葛立恒数

**定义** 定义辅助函数 $G : ℕ → ℕ$, 从4个箭头开始, 迭代 $3 ↑^n 3$ 作为箭头数量, 即

$$
\begin{aligned}
G\kern{0.17em}0 &:= 4 \\
G\kern{0.17em}n^+ &:= 3 ↑^n 3
\end{aligned}
$$

非形式地

$$
G\kern{0.17em}n := 3 ↑^{3 ↑^{... ↑^{3 ↑↑↑↑ 3} ...} 3} 3
$$

则葛立恒数为 $G\kern{0.17em}64$.

```agda
module Graham where
  G : ℕ → ℕ
  G zero = 4
  G (suc n) = 3 ↑⟨ n ⟩ 3

  G64 : ℕ
  G64 = G 64
```

## 康威链箭

**约定** 我们用 $n a_1 a_2 a_3 a_4 b c$ 表示任意自然数.

```agda
private variable n a₁ a₂ a₃ a₄ b c : ℕ
```

```agda
pattern 2+ n = suc (suc n)
pattern 3+ n = suc (suc (suc n))
```

```agda
C₂ : ℕ → ℕ → ℕ
C₂ = _^_

C₃ : ℕ → ℕ → ℕ → ℕ
C₃ a (2+ b) (2+ c) = C₃ a (C₃ a (suc b) (2+ c)) (suc c)
C₃ a b _ = C₂ a b

C₄ : ℕ → ℕ → ℕ → ℕ → ℕ
C₄ a₁ a₂ (2+ b) (2+ c) = C₄ a₁ a₂ (C₄ a₁ a₂ (suc b) (2+ c)) (suc c)
C₄ a₁ a₂ b _ = C₃ a₁ a₂ b

C₅ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
C₅ a₁ a₂ a₃ (2+ b) (2+ c) = C₅ a₁ a₂ a₃ (C₅ a₁ a₂ a₃ (suc b) (2+ c)) (suc c)
C₅ a₁ a₂ a₃ b _ = C₄ a₁ a₂ a₃ b
```

```agda
C₊ : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ
C₊ C a (2+ b) (2+ c) = C₊ C a (C₊ C a (suc b) (2+ c)) (suc c)
C₊ C a b _ = C a b
```

```agda
C₃′ : ℕ → ℕ → ℕ → ℕ
C₃′ = C₊ C₂

C₄′ : ℕ → ℕ → ℕ → ℕ → ℕ
C₄′ a = C₊ (C₃′ a)

C₅′ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
C₅′ a₁ a₂ = C₊ (C₄′ a₁ a₂)
```

```agda
_→ⁿ_ : Set → ℕ → Set
A →ⁿ zero = A
A →ⁿ suc n = ℕ → A →ⁿ n
```

```agda
open import Data.Vec using (Vec; _∷_; [])
```

```agda
curry3 : (Vec ℕ n → ℕ → ℕ → ℕ → ℕ) → ℕ →ⁿ 3+ n
curry3 {n = zero} F = F []
curry3 {n = suc n} F a = curry3 λ a⃗ → F (a ∷ a⃗)

uncurry2 : ℕ →ⁿ 2+ n → (Vec ℕ n → ℕ → ℕ → ℕ)
uncurry2 {n = zero} F [] = F
uncurry2 {n = suc n} F (a ∷ a⃗) = uncurry2 (F a) a⃗
```

```agda
C₂₊ₙ : ℕ →ⁿ 2+ n
C₂₊ₙ {n = 0} = _^_
C₂₊ₙ {n = suc n} = curry3 λ a⃗ → C₊ (uncurry2 C₂₊ₙ a⃗)
```

```agda
_ : C₂₊ₙ {0} b c ≡ b ^ c
_ = refl

_ : C₂₊ₙ {1} 2 2 1 ≡ C₂₊ₙ {0} 2 2
_ = refl

_ : C₂₊ₙ {2} 2 2 1 9 ≡ C₂₊ₙ {0} 2 2
_ = refl

_ : C₂₊ₙ {3} 2 2 2 1 9 ≡ C₂₊ₙ {1} 2 2 2
_ = refl

_ : C₂₊ₙ {4} a₁ a₂ a₃ a₄ (2+ b) (2+ c) ≡ C₂₊ₙ {4} a₁ a₂ a₃ a₄ (C₂₊ₙ {4} a₁ a₂ a₃ a₄ (suc b) (2+ c)) (suc c)
_ = refl
```
