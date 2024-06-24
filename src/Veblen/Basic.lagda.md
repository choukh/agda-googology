---
title: 形式化大数数学 (1.1 - 序数, FGH, 不动点)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.1 - 序数, FGH, 不动点)

> 交流Q群: 893531731  
> 本文源码: [Basic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Basic.lagda.md)  
> 高亮渲染: [Basic.html](https://choukh.github.io/agda-googology/Veblen.Basic.html)  

## 前言

本系列文章是可运行且保证停机的[大数](https://zh.wikipedia.org/wiki/%E5%A4%A7%E6%95%B0_(%E6%95%B0%E5%AD%A6))计算程序的[文学编程 (literate programming)](https://zh.wikipedia.org/wiki/%E6%96%87%E5%AD%A6%E7%BC%96%E7%A8%8B) 实现.

- **可运行**是相对于自然语言的数学描述而言, 本文贴出的代码可以在电脑上运行.
- **保证停机**是相对于[图灵完备 (Turing-complete)](https://zh.wikipedia.org/wiki/%E5%9C%96%E9%9D%88%E5%AE%8C%E5%82%99%E6%80%A7) 语言 (如C语言) 而言, 本文使用的 [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)) 语言并非图灵完备, 其自带[停机检查 (termination checking)](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/termination-checking.html), 写出的程序保证停机.
- **文学编程**是指本文既是程序代码, 也是程序文档, 代码和文档交织在一起, 以增强可读性.
  - Agda 程序会自动抽取本文所有代码块中的代码, 并执行类型检查, 而忽略代码块以外的内容.
  - ※ 冷知识: 文学编程的发明者[高德纳 (Donald Knuth)](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%BA%B3), 也是大数数学入门级内容[高德纳箭号](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%B4%8D%E7%AE%AD%E8%99%9F%E8%A1%A8%E7%A4%BA%E6%B3%95)的发明者, 也是排版软件 [TeX](https://zh.wikipedia.org/wiki/TeX) 的发明者.

也就是说, 提供足够的时间, 能量和内存, 本文介绍的大数计算程序可以真正算出一个大数. 如果真的想运行:
- 关于 Agda 的安装请参考 [Installation](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
- 本文所在Github仓库: [agda-googology](https://github.com/choukh/agda-googology).

### 目标人群

- 大数数学已入门 (如, 看完[大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)), 对严格性有进一步要求的读者.
- Agda 已入门 (如, 看完 [PLFA](https://agda-zh.github.io/PLFA-zh/)), 对大数计算程序的编程实现感兴趣的读者.

只对前者感兴趣的读者, 可以忽略代码部分, 而只阅读文学部分, 它们可以看作是基于朴素类型论的数学描述, 并使用了 $\LaTeX$ 公式, 以对齐通常的数学习惯.

### 补充材料

- [core.exe - 大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)
- [core.exe - 大数数学入门 - 重置版](https://www.zhihu.com/column/c_1697290814588301312)
- [oCaU - Agda大序数](https://zhuanlan.zhihu.com/p/572691308)
  - 详细讨论了上至二元Veblen层级的序性质.
  - ※ 本文不会讨论这些性质.

### 标准库依赖

```agda
module Veblen.Basic where

open import Data.Nat public using (ℕ; zero; suc; 2+)
open import Data.Unit public using (⊤)
open import Function public using (id; _∘_; _$_; _∋_)
open import Relation.Binary.PropositionalEquality as Eq public using (_≡_; refl; cong)
open Eq.≡-Reasoning
```

## 序数的定义

我们知道自然数类型 $ℕ$ 由如下两条规则定义.

$$
\frac{}{~\text{zero} : ℕ~}
\qquad
\frac{\alpha:ℕ}{~\text{suc}~\alpha:ℕ~}
$$

我们的序数类型 $\text{Ord}$ 则在此基础上增加了第三条规则 $\text{lim}$, 即如果 $f$ 是 $ℕ$ 到序数的函数, 那么 $\text{lim}~f$ 也是序数.

$$
\frac{}{~\text{zero} : \text{Ord}~}
\qquad
\frac{\alpha:\text{Ord}}{~\text{suc}~\alpha:\text{Ord}~}
\qquad
\frac{~f : ℕ\rightarrow\text{Ord}~}{\text{lim}~f:\text{Ord}}
$$

```agda
data Ord : Set where
  zero : Ord
  suc  : Ord → Ord
  lim  : (ℕ → Ord) → Ord
```

这样的 $f : ℕ\rightarrow\text{Ord}$ 又叫做 $\text{lim}~f$ 的基本序列 (fundamental sequence), 而 $\text{lim}~f$ 则叫做基本序列 $f$ 的极限. 这样的定义允许我们很方便地讨论零, 后继序数和极限序数三种情况. 为了方便阅读, 我们会把 $\text{zero}$ 写作 $0$, 把 $\text{suc}~x$ 写作 $x^+$.

**注意** 我们的序数类型, 学名叫布劳威尔树序数 (Brouwer tree ordinals), 比真正的序数宽泛很多, 体现在以下两点:
- 树序数不要求基本序列是严格递增的.
  - 严格递增的约束对于大数的计算本身而言无关紧要.
  - 我们构造的序数的基本序列都是严格递增的, 如果想要, 可以额外补上证明.
  - [Agda大序数](https://zhuanlan.zhihu.com/p/572691308)一文中证明了其中构造的上至 $\Gamma_0$ 的所有树序数的基本序列都是严格递增的.
- 树序数是外延的 (extensional), 即真正的序数与树上的节点并不是唯一对应的.
  - 这意味着我们可以用不同的基本序列构造出相同的序数.
    - 但同一性证明依赖于函数外延性 (function extensionality), 或某种商 (quotient) 机制, 如 setoid 或 cubical.
  - 但这并不会影响大数的计算, 因为只要给出基本序列就能算, 况且大数的表示确实是依赖于特定的基本序列的.

我们约定用 $α,β,γ,δ$ 表示序数, 用 $m,n$ 表示自然数.

```agda
variable
  α β γ δ : Ord
  m n : ℕ
```

我们可以定义自然数到序数的嵌入函数 $\text{finord} : ℕ → \text{Ord}$ 如下 (注意: 遵循类型论的习惯, 我们今后都会在无歧义的情况下省略函数应用的括号).

$$
\begin{aligned}
\text{finord}~0 &= 0 \\
\text{finord}~n^+ &= (\text{finord}~n)^+
\end{aligned}
$$

```agda
finord : ℕ → Ord
finord zero = zero
finord (suc n) = suc (finord n)
```

$\text{finord}$ 构成了基本序列 $(0, 1, 2, \ldots)$, 其极限定义为 $ω$.

$$
ω := \text{lim}~\text{finord}
$$

```agda
ω = lim finord
```

以下代码调用了[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能, 允许数字字面量依据上下文自动具有自然数或序数类型.

```agda
open import Agda.Builtin.FromNat

instance
  _ = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord n }
  _ = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
```

以下为测试用例.

```agda
_ = Ord ∋ 233
_ = ℕ   ∋ 233
```

## 快速增长层级

```agda
variable A : Set
```

```agda
_∘ⁿ_ : (A → A) → ℕ → (A → A)
(F ∘ⁿ zero)  a = a
(F ∘ⁿ suc n) a = (F ∘ (F ∘ⁿ n)) a
```

```agda
module FGH where
  f : Ord → ℕ → ℕ
  f zero n = suc n
  f (suc α) n = (f α ∘ⁿ n) n
  f (lim g) n = f (g n) n
```

$$
f_0(n) = n + 1
$$

```agda
  f-0-2 : f 0 2 ≡ 3
  f-0-2 = refl
```

$$
f_1(n) = 2n
$$

```agda
  f-1-2 : f 1 2 ≡ 4
  f-1-2 = refl
```

$$
f_2(n) = 2^n~n
$$

```agda
  f-2-2 : f 2 2 ≡ 8
  f-2-2 = refl
```

```agda
  f-3-2 : f 3 2 ≡ 2048
  f-3-2 = refl
```

```agda
  f-suc : f (suc α) n ≡ (f α ∘ⁿ n) n
  f-suc = refl
```

```agda
  f-ω : f ω n ≡ f (finord n) n
  f-ω = refl
```

```agda
  f-ω⁺ : f (suc ω) n ≡ (f ω ∘ⁿ n) n
  f-ω⁺ = refl
```

```agda
  f-suc-2 : f (suc α) 2 ≡ f α (f α 2)
  f-suc-2 = refl
```

`f (suc ω) 64` 大于葛立恒数.

## 无穷迭代

```agda
elim : {P : Ord → Set}
  → P zero
  → (∀ α → P α → P (suc α))
  → (∀ f → (∀ n → P (f n)) → P (lim f))
  → ∀ α → P α
elim z s l zero = z
elim z s l (suc α) = s α (elim z s l α)
elim z s l (lim f) = l f λ n → elim z s l (f n)
```

```agda
rec : A → (A → A) → ((ℕ → A) → A) → Ord → A
rec z s l = elim z (λ _ → s) (λ _ → l)
```

```agda
_∘^_ : (Ord → Ord) → Ord → Ord → Ord
(F ∘^ α) β = rec β F lim α
```

```agda
variable
  F : Ord → Ord
  f g h : ℕ → Ord
```

```agda
∘^-zero : F ∘^ zero ≡ id
∘^-zero = refl
```

```agda
∘^-suc : F ∘^ suc α ≡ F ∘ (F ∘^ α)
∘^-suc = refl
```

```agda
∘^-lim : F ∘^ lim f ≡ λ β → lim λ n → (F ∘^ (f n)) β
∘^-lim = refl
```

```agda
iterω : (Ord → Ord) → Ord → Ord
iterω F α = (F ∘^ ω) α
```

## 序数算术

```agda
infixl 6 _+_
_+_ : Ord → Ord → Ord
α + β = (suc ∘^ β) α
```

```agda
infixl 7 _*_
_*_ : Ord → Ord → Ord
α * β = ((_+ α) ∘^ β) 0
```

```agda
infix 8 _^_
_^_ : Ord → Ord → Ord
α ^ β = ((_* α) ∘^ β) 1
```

```agda
_+ω^_ : Ord → Ord → Ord
α +ω^ zero = suc α
α +ω^ suc β = iterω (_+ω^ β) α
α +ω^ lim f = lim λ n → α +ω^ f n
```

## 跳出运算

复合了后继的迭代.

```agda
jump : (Ord → Ord) → Ord → Ord
jump F α = ((F ∘ suc) ∘^ α) (F zero)
```

```agda
jump-0 : jump F 0 ≡ F 0
jump-0 = refl
```

```agda
jump-suc : jump F (suc α) ≡ F (suc (jump F α))
jump-suc {F} {α} = begin
  jump F (suc α)                        ≡⟨⟩
  ((F ∘ suc) ∘^ (suc α)) (F zero)       ≡⟨⟩
  (F ∘ suc) (((F ∘ suc) ∘^ α) (F zero)) ≡⟨⟩
  F (suc (jump F α))                    ∎
```

```agda
jump-lim : jump F (lim f) ≡ lim λ n → jump F (f n)
jump-lim = refl
```

## 不动点的枚举

```agda
fixpt : (Ord → Ord) → Ord → Ord
fixpt F = jump (iterω F)
```

```agda
fixpt-0 : fixpt F 0 ≡ iterω F 0
fixpt-0 = refl
```

```agda
fixpt-suc : fixpt F (suc α) ≡ iterω F (suc (fixpt F α))
fixpt-suc {F} {α} = refl
```

```agda
fixpt-lim : fixpt F (lim f) ≡ lim λ n → fixpt F (f n)
fixpt-lim = refl
```

## ε， ζ， η 层级

```agda
ε : Ord → Ord
ε = fixpt (ω ^_)
```

```agda
ε-0 : ε 0 ≡ iterω (ω ^_) 0
ε-0 = refl
```

```agda
ε-suc : ε (suc α) ≡ iterω (ω ^_) (suc (ε α))
ε-suc = refl
```

```agda
ε-lim : ε (lim f) ≡ lim λ n → ε (f n)
ε-lim = refl
```

```agda
ζ : Ord → Ord
ζ = fixpt ε
```

```agda
η : Ord → Ord
η = fixpt ζ
```
