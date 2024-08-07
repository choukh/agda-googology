---
title: 形式化大数数学 (1.0 - 序数, 增长层级, 不动点)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/705306447
---

# 形式化大数数学 (1.0 - 序数, 增长层级, 不动点)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-googology/Veblen.Base.html)  

## 前言

本系列文章是可运行且保证停机的[大数](https://zh.wikipedia.org/wiki/%E5%A4%A7%E6%95%B0_(%E6%95%B0%E5%AD%A6))计算程序的[文学编程 (literate programming)](https://zh.wikipedia.org/wiki/%E6%96%87%E5%AD%A6%E7%BC%96%E7%A8%8B) 实现.

- **可运行**是相对于自然语言的数学描述而言, 本文贴出的代码可以在电脑上运行.
- **保证停机**是相对于[图灵完备 (Turing-complete)](https://zh.wikipedia.org/wiki/%E5%9C%96%E9%9D%88%E5%AE%8C%E5%82%99%E6%80%A7) 语言 (如C语言) 而言, 本文使用的 [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)) 语言并非图灵完备, 其自带[停机检查 (termination checking)](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/termination-checking.html), 写出的程序保证停机.
- **文学编程**是指本文既是程序代码, 也是程序文档, 代码和文档交织在一起, 以增强可读性.
  - Agda 程序会自动抽取本文所有代码块中的代码, 并执行类型检查, 而忽略代码块以外的内容.
  - ※ 冷知识: 文学编程的发明者[高德纳 (Donald Knuth)](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%BA%B3), 也是大数数学入门级内容[高德纳箭号](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%B4%8D%E7%AE%AD%E8%99%9F%E8%A1%A8%E7%A4%BA%E6%B3%95)的发明者, 也是排版软件 [TeX](https://zh.wikipedia.org/wiki/TeX) 的发明者.
  - Agda代码将放在如下代码块中

```agda
{-# OPTIONS --safe #-}
module Veblen.Base where
```

也就是说, 提供足够的时间, 能量和内存, 本文介绍的大数计算程序可以真正算出一个大数. 如果真的想运行:
1. 参考 [Installation](https://agda.readthedocs.io/en/latest/getting-started/installation.html) 安装 Agda.
2. 进本文所在Github仓库 ([agda-googology](https://github.com/choukh/agda-googology)) 下载本文 markdown 源码.
3. 用编辑器打开源码, 确认进入了 [agda-mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html), 键入 `C-c C-n` 对本文定义的任意大数 (如文末的 `oom`) 执行正规化 (normalization).

### 目标人群

- 大数数学已入门 (如, 看完[大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)), 对严格性和精确定义有进一步要求的读者.
- Agda 已入门 (如, 看完 [PLFA](https://agda-zh.github.io/PLFA-zh/)), 对大数计算程序的编程实现感兴趣的读者.

只对前者感兴趣的读者, 可以忽略代码部分, 而只阅读文学部分, 它们可以看作是基于朴素类型论的数学描述, 并使用了 $\LaTeX$ 公式, 以对齐通常的数学习惯.

### 补充材料

- [core.exe - 大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)
- [core.exe - 大数数学入门 - 重置版](https://www.zhihu.com/column/c_1697290814588301312)
- [oCaU - Agda大序数](https://zhuanlan.zhihu.com/p/572691308)
  - 详细讨论了上至二元Veblen层级的序性质, 而本文不会讨论这些性质
- [oCaU - Googology](https://github.com/choukh/Googology)
  - 包含上一条的 Coq 版本以及 LVO 的 Coq 实现
  - 纯代码, 无文学
- [ccz181078 - googology](https://github.com/ccz181078/googology)
  - 各种大数函数的 Coq 形式化
  - 有少量注释, 适合上级者速通形式化定义

### 标准库依赖

```agda
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Unit public using (⊤; tt)
open import Function public using (id; _∘_; _$_; _∋_)
open import Relation.Binary.PropositionalEquality as Eq public using (_≡_; refl)
open Eq.≡-Reasoning public
```

## 序数的定义

我们知道自然数类型 $ℕ$ 由如下两条规则定义.

$$
\frac{}{\kern{0.17em}\text{zero} : ℕ\kern{0.17em}}
\qquad
\frac{\alpha:ℕ}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:ℕ\kern{0.17em}}
$$

**定义** 我们的序数类型 $\text{Ord}$ 在 $ℕ$ 的基础上增加了第三条规则 $\text{lim}$, 即如果 $f$ 是 $ℕ$ 到序数的函数, 那么 $\text{lim}\kern{0.17em}f$ 也是序数.

$$
\frac{}{\kern{0.17em}\text{zero} : \text{Ord}\kern{0.17em}}
\qquad
\frac{\alpha:\text{Ord}}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:\text{Ord}\kern{0.17em}}
\qquad
\frac{\kern{0.17em}f : ℕ\rightarrow\text{Ord}\kern{0.17em}}{\text{lim}\kern{0.17em}f:\text{Ord}}
$$

```agda
data Ord : Set where
  zero : Ord
  suc  : Ord → Ord
  lim  : (ℕ → Ord) → Ord
```

这样的 $f : ℕ\rightarrow\text{Ord}$ 又叫做 $\text{lim}\kern{0.17em}f$ 的基本列 (fundamental sequence), 而 $\text{lim}\kern{0.17em}f$ 则叫做基本列 $f$ 的极限. 仅就我们将要做的事情而言, $\lim$ 可视为等同于集合论的 $\sup$. 这样的定义允许我们很方便地讨论零, 后继序数和极限序数三种情况. 为了方便阅读, 我们会把 $\text{zero}$ 写作 $0$, 把 $\text{suc}\kern{0.17em}x$ 写作 $x^+$.

**注意** 我们的序数类型, 学名叫布劳威尔树序数 (Brouwer tree ordinals), 比真正的递归序数宽泛很多, 体现在以下两点:

- 树序数不要求基本列是严格递增的.
  - 严格递增的约束对于计算本身而言无关紧要.
  - 当然, 如果要保证算出的大数足够大, 那么基本列的递增性是必要的.
  - 我们构造的序数的基本列都是严格递增的, 如果想要, 可以额外补上证明.
  - [Agda大序数](https://zhuanlan.zhihu.com/p/572691308)一文中证明了其中构造的上至 $\Gamma_0$ 的所有树序数的基本列都是严格递增的.
- 树序数是高度外延的 (extensional), 即一个真正的递归序数可能对应树上大量的节点.
  - 也就是说我们可以用大量不同的基本列构造出相同的序数.
    - 但同一性证明依赖于函数外延性 (functional extensionality), 或某种商 (quotient) 机制, 如 setoid 或 cubical.
  - 但这并不影响大数的计算, 因为只要给出基本列就能算, 况且 FGH 大数的具体数值确实可能是依赖于特定基本列的——同一序数的不同定义方式会使基本列在起始处稍有不同.

**约定** 我们用 $α,β,γ$ 表示序数, 用 $n$ 表示自然数, 用 $A$ 表示任意给定的类型.

```agda
variable
  α β γ : Ord
  n : ℕ
  A : Set
```

**约定** 我们遵循类型论的习惯, 今后都会在无歧义的情况下省略函数应用的括号.

回忆任意类型 $A$ 上的函数的有限次迭代.

**定义** 函数 $F : A → A$ 的 $n$ 次复合叫做 $F$ 的 $n$ 次迭代, 记作 $F^n$

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{n^+} &= F \circ F^n
\end{aligned}
$$

其中 $\text{id}$ 是恒等函数.

```agda
open import Lower public using (_∘ⁿ_)
```

**定义** 自然数到序数的嵌入函数 $\text{finord} : ℕ → \text{Ord}$ 定义为对输入的自然数 $n$, 输出从序数零开始迭代序数后继 $n$ 次所得到的序数.

$$
\text{finord}\kern{0.17em}n := \text{suc}^n\kern{0.17em}0
$$

```agda
finord : ℕ → Ord
finord n = (suc ∘ⁿ n) zero
```

**定义** $\text{finord}$ 构成了基本列 $(0, 1, 2, \ldots)$, 其极限定义为 $ω$

$$
ω := \text{lim}\kern{0.17em}\text{finord}
$$

```agda
ω = lim finord
```

**非文学** 以下代码调用了[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能, 允许数字字面量依据上下文自动具有自然数或序数类型.

```agda
open import Agda.Builtin.FromNat public
instance
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → finord n }
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
```

以下为测试用例.

```agda
_ = Ord ∋ 233
_ = ℕ   ∋ 233
```

**非文学** 我们将 `suc (suc α)` 写作 `2+ α`.

```agda
pattern 2+ α = suc (suc α)
```

## 增长层级

增长层级是一种函数族 $f : \text{Ord} → ℕ → ℕ$, 对于每个序数 $α$, $f_α$ 是一个从自然数到自然数的函数. 最常用的是快速增长层级.

### 快速

**定义** 快速增长层级 (Fast Growing Hierarchy, FGH)

$$
\begin{aligned}
f_0 &= \text{suc} \\
f_{α^+}\kern{0.17em}n &= f_α^n\kern{0.17em}n \\
f_{\text{lim}\kern{0.17em}α}\kern{0.17em}n &= f_{α[n]}\kern{0.17em}n
\end{aligned}
$$

其中在极限序数情况下的这种处理方式叫做对角化 (diagonalization).

```agda
module FGH where
  f : Ord → ℕ → ℕ
  f zero = suc
  f (suc α) n = (f α ∘ⁿ n) n
  f (lim α) n = f (α n) n
```

**例** 我们有

$$
\begin{aligned}
f_0\kern{0.17em}n &= n^+ \\
f_1\kern{0.17em}n &= 2n \\
f_2\kern{0.17em}n &= 2^n\kern{0.17em}n
\end{aligned}
$$

这些等式的证明只需对 $n$ 进行归纳, 是显然的. 代码方面我们只写一些实例作为测试.

```agda
  f-0-2 : f 0 2 ≡ 3
  f-0-2 = refl

  f-1-2 : f 1 2 ≡ 4
  f-1-2 = refl

  f-2-2 : f 2 2 ≡ 8
  f-2-2 = refl
```

$f_3$ 以上的表达式越来越复杂, 但不难计算实例如 $f_{3}\kern{0.17em}2=2048$.

```agda
  f-3-2 : f 3 2 ≡ 2048
  f-3-2 = refl
```

**引理** 我们有

$$
\begin{aligned}
f_{\alpha^+}\kern{0.17em}n &= f_\alpha^n\kern{0.17em}n \\
f_{ω}\kern{0.17em}n &= f_{n}\kern{0.17em}n
\end{aligned}
$$

```agda
  f-suc : f (suc α) n ≡ (f α ∘ⁿ n) n
  f-suc = refl

  f-ω : f ω n ≡ f (finord n) n
  f-ω = refl
```

**注意** 本文出现的大部分命题的证明都是「依定义即得」的, 体现为代码中的 `refl`. 也就是说, 证明都是直接展开定义, 不需要额外的推理. 但这并不意味着所有证明是显然的, 有时候递归定义的展开会非常复杂, 这时候我们会分步展开, 逐步化简, 但每一步都 `refl` 可证.

**定理** 由以上两式不难看出

$$
f_{ω^+}\kern{0.17em}n = f_ω^n\kern{0.17em}n
$$

```agda
  f-ω⁺ : f (suc ω) n ≡ (f ω ∘ⁿ n) n
  f-ω⁺ = refl
```

**推论** 特别地, 有

$$
f_{ω^+}\kern{0.17em}2 = f_ω\kern{0.17em}(f_ω\kern{0.17em}2)
$$

但此式无法在 Agda 中直接证明, 因为 Agda 想先把两边都算出再比较相等, 而这是不现实的. 如果有读者知道如何证明, 请打在评论区. 作为替代, 我们可以证明如下式子.

$$
f_{\alpha^+}\kern{0.17em}2 = f_\alpha\kern{0.17em}(f_\alpha\kern{0.17em}2)
$$

```agda
  f-suc-2 : f (suc α) 2 ≡ f α (f α 2)
  f-suc-2 = refl
```

**事实** $f_{ω^+} 64$ 已经大于葛立恒数.

> 从这里开始, 研究大数的数学就转变成了研究快速增长函数的数学, 进而转变成研究大的序数的数学.

### ※快速以下

FGH 是最常用的增长层级, 除此之外, 其他常见的还有 SGH, MGH, HH. 它们的共同特征是遇到极限序数都要做对角化.

**定义** 慢速增长层级 SGH

$$
\begin{aligned}
g_0\kern{0.17em}n &= 0 \\
g_{α^+}\kern{0.17em}n &= (g_α\kern{0.17em}n)^+ \\
g_{\text{lim}\kern{0.17em}α}\kern{0.17em}n &= g_{α[n]}\kern{0.17em}n
\end{aligned}
$$

```agda
module SGH where
  g : Ord → ℕ → ℕ
  g zero _ = 0
  g (suc α) n = suc (g α n)
  g (lim α) n = g (α n) n
```

**定义** 中速增长层级 MGH

$$
\begin{aligned}
m_0 &= \text{suc} \\
m_{α^+} &= m_α^2 \\
m_{\text{lim}\kern{0.17em}α}\kern{0.17em}n &= m_{α[n]}\kern{0.17em}n
\end{aligned}
$$

```agda
module MGH where
  m : Ord → ℕ → ℕ
  m zero = suc
  m (suc α) = m α ∘ⁿ 2
  m (lim α) n = m (α n) n
```

**定义** Hardy层级 HH, 介于中速和慢速之间

$$
\begin{aligned}
h_0 &= \text{id} \\
h_{α^+}\kern{0.17em}n &= h_α\kern{0.17em}(n^+) \\
h_{\text{lim}\kern{0.17em}α}\kern{0.17em}n &= h_{α[n]}\kern{0.17em}n
\end{aligned}
$$

```agda
module HH where
  h : Ord → ℕ → ℕ
  h zero = id
  h (suc α) n = h α (suc n)
  h (lim α) n = h (α n) n
```

## 序数的递归原理

为了系统性的构造大序数, 我们先证明序数归纳法, 并由此得到序数的递归原理.

**定理 序数归纳法 (transfinite induction)** 对于任意性质 $P : \text{Ord} → \text{Set}$, 如果

1. $P\kern{0.17em}0$ 成立,
2. 对于任意序数 $α$, 如果 $P\kern{0.17em}α$ 成立, 则 $P\kern{0.17em}α^+$ 成立,
3. 对于任意基本列 $f$, 如果对于任意自然数 $n$, $P\kern{0.17em}(f\kern{0.17em}n)$ 成立, 则 $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立,

则对于任意序数 $α$, $P\kern{0.17em}α$ 成立.

```agda
ind : {P : Ord → Set}
  → P zero
  → (∀ α → P α → P (suc α))
  → (∀ f → (∀ n → P (f n)) → P (lim f))
  → ∀ α → P α
```

**(证明)** 要证对于任意序数 $α$, $P\kern{0.17em}α$ 成立. 归纳 $α$ 的三种情况.

- 当 $α=0$ 时, 由条件1, $P\kern{0.17em}0$ 成立.
- 当 $α=α^+$ 时, 要证 $P\,α^+$ 成立. 由归纳假设, $P\kern{0.17em}α$ 成立. 由条件2, $P\kern{0.17em}α^+$ 成立.
- 当 $α=\text{lim}\kern{0.17em}f$ 时, 要证 $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立. 由归纳假设, 对于任意自然数 $n$, $P\kern{0.17em}(f\kern{0.17em}n)$ 成立. 由条件3, $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立. ∎

```agda
ind z s l zero = z
ind z s l (suc α) = s α (ind z s l α)
ind z s l (lim f) = l f λ n → ind z s l (f n)
```

**注意** 这里看起来像是循环论证, 我们实际做的事情是从类型论承诺的规则中抽取出对 $\text{Ord}$ 单独适用的部分, 并固化为了一个高阶函数 $\text{ind}$.

**定理 序数的递归原理 (transfinite recursion)** 对于任意类型 $A$, 函数 $z : A$, $s : A → A$, $l : (ℕ → A) → A$, 和任意序数 $α$, 存在唯一的 $\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α : A$, 满足

$$
\begin{aligned}
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}0 &= z \\
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α^+ &= s\kern{0.17em}(\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α) \\
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}(\text{lim}\kern{0.17em}f) &= l\kern{0.17em}(λ\kern{0.17em}n,\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}(f\kern{0.17em}n))
\end{aligned}
$$

**(证明)** 令 $P = λ\kern{0.17em}\_,A$ 并应用序数归纳法即可. ∎

```agda
rec : A → (A → A) → ((ℕ → A) → A) → Ord → A
rec z s l = ind z (λ _ → s) (λ _ → l)
```

**注意** 序数的递归原理和序数归纳法都可视作高阶函数, 递归原理是归纳法的特例.

**注意** 序数的递归原理相当强大, 因为 $A$ 可以是任意类型, 包括函数类型 $\text{Ord}\rightarrow\text{Ord}$ 与 $(\text{Ord}\rightarrow\text{Ord})\rightarrow(\text{Ord}\rightarrow\text{Ord})$ 等, 也就是说它允许定义高阶函数的递归. 本文出现的所有大序数都由 $\text{rec}$ 定义.

## 超限复合

**约定** 我们用 $F$ 表示序数函数 $\text{Ord} → \text{Ord}$, 用 $f,g,h$ 表示基本列 $ℕ → \text{Ord}$.

```agda
variable
  F : Ord → Ord
  f g h : ℕ → Ord
```

**定义** 仿照函数 $F : A → A$ 的 $n$ 次复合 $F^n$, 我们定义序数函数 $F : \text{Ord} → \text{Ord}$ 的 $α$ 次复合 $F^α$, 但使用序数的递归原理 $\text{rec}$ 来定义.

$$
F^\alpha\kern{0.17em}\beta=\text{rec}\kern{0.17em}\beta\kern{0.17em}F\kern{0.17em}\text{lim}\kern{0.17em}\alpha
$$

```agda
_∘^_ : (Ord → Ord) → Ord → Ord → Ord
(F ∘^ α) β = rec β F lim α
```

**注意** 该定义不是 $F^\alpha\kern{0.17em}\beta=\text{rec}\kern{0.17em}\beta\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}\alpha)$, 此式有类型错误.

对于 $\text{rec}$ 的四个参数, 直观上

- 第一个参数是初始值, 这里是 $F^\alpha$ 的输入 $\beta$,
- 第二个参数是后继步骤, 需要指定递归迭代的函数, 这里递归迭代的就是 $F$,
- 第三个参数是极限步骤, 需要指定将极限步对应的步骤基本列 $λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta$ 映射到序数的函数, 这里就是单纯地取其极限, 所以指定为 $\text{lim}$,
- 第四个参数是递归的次数, 这里是 $\alpha$.

**定理** 依定义有

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{α^+} &= F \circ F^α \\
F^{\text{lim}\kern{0.17em}f} &= λ\kern{0.17em}\beta,\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta
\end{aligned}
$$

```agda
∘^-zero : F ∘^ zero ≡ id
∘^-zero = refl

∘^-suc : F ∘^ suc α ≡ F ∘ (F ∘^ α)
∘^-suc = refl

∘^-lim : F ∘^ lim f ≡ λ β → lim λ n → (F ∘^ (f n)) β
∘^-lim = refl
```

**注意** $λ\kern{0.17em}\beta,\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta$ 不能简化成 $\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}$, 此式有类型错误.

## 序数算术

**定义** 从 $α$ 开始做 $β$ 次后继叫做序数加法, 记作 $α+β$

$$
α + β := \text{suc}^β\kern{0.17em}α
$$

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
α + β = (suc ∘^ β) α
```

**定义** 从 $0$ 开始做 $β$ 次 $+ α$ 叫做序数乘法, 记作 $α×β$

$$
α × β := (λξ,ξ+α)^β\kern{0.17em}0
$$

```agda
_*_ : Ord → Ord → Ord; infixl 7 _*_
α * β = ((_+ α) ∘^ β) 0
```

**定义** 从 $1$ 开始做 $β$ 次 $× α$ 叫做序数幂运算, 记作 $α^β$

$$
α^β := (λξ,ξ×α)^β\kern{0.17em}1
$$

```agda
_^_ : Ord → Ord → Ord; infix 8 _^_
α ^ β = ((_* α) ∘^ β) 1
```

关于为什么不能定义序数的第四级运算的原因可以参看[Agda大序数(6) 迭代幂次](https://zhuanlan.zhihu.com/p/580526275).

## 三大高阶函数

Veblen层级的构造需要三个重要的高阶函数

1. 无穷迭代 $λF,F^\omega$
2. 跳出运算 $\text{jump}$
3. 不动点的枚举 $\text{fixpt}$

它们都具有类型 $(\text{Ord}→\text{Ord})→(\text{Ord}→\text{Ord})$.

### 无穷迭代

**定义** 我们称 $F$ 的 $\omega$ 次复合 $F^\omega$ 为 $F$ 的无穷迭代.

```agda
iterω : (Ord → Ord) → Ord → Ord
iterω F = F ∘^ ω
```

### 跳出运算

**定义** 给定序数函数 $F$, 起始值 $ι$ 和迭代次数 $α$, 从 $F\kern{0.17em}ι$ 开始, 每次迭代时先做一次后继再迭代 $F$, 总共迭代 $α$ 次的运算叫做 $F$ 的从 $ι$ 开始的 $α$ 次跳出, 记作 $\text{jump}_ι\kern{0.17em}F\kern{0.17em}α$.

$$
\text{jump}_ι\kern{0.17em}F\kern{0.17em}α := (F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^α\kern{0.17em}(F\kern{0.17em}ι)
$$

```agda
jump⟨_⟩ : Ord → (Ord → Ord) → Ord → Ord
jump⟨ ι ⟩ F α = ((F ∘ suc) ∘^ α) (F ι)
```

我们通常只会使用 $ι = 0$ 的版本 $\text{jump}_0\kern{0.17em}F\kern{0.17em}α$, 简记作 $\text{jump}\kern{0.17em}F\kern{0.17em}α$.

```agda
jump : (Ord → Ord) → Ord → Ord
jump F = jump⟨ 0 ⟩ F
```

**定理** 依定义有

$$
\begin{aligned}
\text{jump}\kern{0.17em}F\kern{0.17em}0 &= F\kern{0.17em}0 \\
\text{jump}\kern{0.17em}F\kern{0.17em}(α^+) &= F\kern{0.17em}(\text{jump}\kern{0.17em}F\kern{0.17em}α)^+ \\
\text{jump}\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}f) &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\text{jump}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)
\end{aligned}
$$

**(证明)** 零和极限的情况是显然的. 对于后继的情况, 有

$$
\begin{aligned}
\text{jump}\kern{0.17em}F\kern{0.17em}(α^+) &= (F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^{α^+}\kern{0.17em}(F\kern{0.17em}0) \\
&= (F\kern{0.17em}\circ\kern{0.17em}\text{suc})((F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^α\kern{0.17em}(F\kern{0.17em}0)) \\
&= F\kern{0.17em}(\text{jump}\kern{0.17em}F\kern{0.17em}α)^+
\end{aligned}
$$

∎

```agda
jump-0 : jump F 0 ≡ F 0
jump-0 = refl

jump-suc : jump F (suc α) ≡ F (suc (jump F α))
jump-suc {F} {α} = begin
  jump F (suc α)                        ≡⟨⟩
  ((F ∘ suc) ∘^ (suc α)) (F zero)       ≡⟨⟩
  (F ∘ suc) (((F ∘ suc) ∘^ α) (F zero)) ≡⟨⟩
  F (suc (jump F α))                    ∎

jump-lim : jump F (lim f) ≡ lim λ n → jump F (f n)
jump-lim = refl
```

### 不动点的枚举

**定义** 给定序数函数 $F$, 我们定义 $F$ 的第 $α$ 个不动点 $\text{fixpt}\kern{0.17em}F\kern{0.17em}α$ 为 $F^\omega$ 的第 $α$ 个跳出 $\text{jump}\kern{0.17em}(F^\omega)\kern{0.17em}α$.

$$
\text{fixpt}\kern{0.17em}F := \text{jump}\kern{0.17em}(F^\omega)
$$

```agda
fixpt : (Ord → Ord) → Ord → Ord
fixpt F = jump (iterω F)
```

特别地, $F$ 的最小的不动点记作 $\text{lfp}\kern{0.17em}F$

$$
\text{lfp}\kern{0.17em}F := \text{fixpt}\kern{0.17em}F\kern{0.17em}0
$$

```agda
lfp : (Ord → Ord) → Ord
lfp F = fixpt F 0
```

**定理** 依定义有

$$
\begin{aligned}
\text{fixpt}\kern{0.17em}F\kern{0.17em}0 &= F^\omega\kern{0.17em}0 \\
\text{fixpt}\kern{0.17em}F\kern{0.17em}(α^+) &= F^\omega\kern{0.17em}(\text{fixpt}\kern{0.17em}F\kern{0.17em}α)^+ \\
\text{fixpt}\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}f) &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\text{fixpt}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)
\end{aligned}
$$

```agda
fixpt-0 : fixpt F 0 ≡ iterω F 0
fixpt-0 = refl

fixpt-suc : fixpt F (suc α) ≡ iterω F (suc (fixpt F α))
fixpt-suc {F} {α} = refl

fixpt-lim : fixpt F (lim f) ≡ lim λ n → fixpt F (f n)
fixpt-lim = refl
```

**注意** 跳出运算并非一定搭配无穷迭代使用, 但一定会搭配极限使用. 后面我们会看到多种 $\text{lim}$ 的情况需要跳出, 以提高增长率.

## ε， ζ， η 层级

我们定义三个序数函数 $\varepsilon, \zeta, \eta$ 如下.

**定义** $\varepsilon$ 是函数 $λα,ω^α$ 的不动点枚举

$$
ε := \text{fixpt}\kern{0.17em}λα,ω\kern{0.17em}^α
$$

```agda
ε : Ord → Ord
ε = fixpt (ω ^_)
```

**定理** 依定义有

$$
\begin{aligned}
\varepsilon_0 &= (λα,ω^α)^ω\kern{0.17em}0 = 
ω^{ω^{⋰^{ω^0}}}
\\
\varepsilon_{α^+} &= (λα,ω^α)^ω\kern{0.17em}({ε_α}^+) = 
ω^{ω^{⋰^{ω^{({ε_α}^+)}}}}
\\
\varepsilon_{\text{lim}\kern{0.17em}f} &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\varepsilon_{f\kern{0.17em}n} = \text{lim}(ε_{f\kern{0.17em}0},ε_{f\kern{0.17em}1},...)
\end{aligned}
$$

```agda
ε-0 : ε 0 ≡ iterω (ω ^_) 0
ε-0 = refl

ε-suc : ε (suc α) ≡ iterω (ω ^_) (suc (ε α))
ε-suc = refl

ε-lim : ε (lim f) ≡ lim λ n → ε (f n)
ε-lim = refl
```

**定义** $\zeta$ 是 $ε$ 的不动点枚举

$$
ζ := \text{fixpt}\kern{0.17em}ε
$$

```agda
ζ : Ord → Ord
ζ = fixpt ε
```

**定理** 依定义有

$$
\begin{aligned}
\zeta_0 &= ε^ω\kern{0.17em}0 =
ε_{ε_{⋱_{ε_0}}}
\\
\zeta_{α^+} &= ε^ω\kern{0.17em}({\zeta_α}^+) =
ε_{ε_{⋱_{({\zeta_α}^+)}}}
\\
\zeta_{\text{lim}\kern{0.17em}f} &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\zeta_{f\kern{0.17em}n} = \text{lim}(ζ_{f\kern{0.17em}0},ζ_{f\kern{0.17em}1},...)
\end{aligned}
$$

**定义** $\eta$ 是 $\zeta$ 的不动点枚举

$$
η := \text{fixpt}\kern{0.17em}ζ
$$

```agda
η : Ord → Ord
η = fixpt ζ
```

**例** 一个很大的大数:

$$
\text{oom} := f_{η_0} 99 = f_{
  ζ_{ζ_{⋱_{ζ_0}}}
}99
$$

其中 $ζ_{ζ_{⋱_{ζ_0}}}$ 是从 $ζ_0$ 开始迭代了 99 次 $ζ$.

```agda
oom = FGH.f (η 0) 99
```
