---
title: 形式化大数数学 (1.3 - 有限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/705994456
---

# 形式化大数数学 (1.3 - 有限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Finitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Finitary.lagda.md)  
> 高亮渲染: [Finitary.html](https://choukh.github.io/agda-googology/Veblen.Finitary.html)  

```agda
{-# OPTIONS --lossy-unification --rewriting --local-confluence-check #-}
module Veblen.Finitary where
open import Veblen.Multinary public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
```

前篇我们讲了二元, 三元和四元Veblen函数 $\text{Bin}.φ,\text{Tri}.φ,\text{Qua}.φ$. 我们希望把元数作为一个参数, 也就是说, 定义一个函数族 $φ$, 使得 $φ_n$ 正好是 $n$ 元Veblen函数. 这样的 $φ$ 叫做 (任意) 有限元Veblen函数 (Finitary Veblen Function), 也叫扩展Veblen函数 (Extended Veblen Function).

```agda
module Bin = BinaryVeblen
module Tri = TrinaryVeblen
module Qua = QuaternaryVeblen
```

## 有限元函数类型

首先我们要把 $φ$ 的类型写出来, 它是一个依赖类型 $\Pi_{n:ℕ}\text{Ord}^{→n}$, 其中 $\text{Ord}^{→n}$ 表示 $\text{Ord}$ 上的 $n$ 元函数类型 $\overbrace{\text{Ord}→...→\text{Ord}}^n →\text{Ord}$. 当然我们也可以采用 $\text{Ord}^n →\text{Ord}$, 即 ($\overbrace{\text{Ord}\times...\times\text{Ord}}^n)→\text{Ord}$. 我们选择前者是因为它有方便的[柯里化 (Currying)](https://en.wikipedia.org/wiki/Currying) 性质, 处理起来更简单.

**定义** 陪域为 $A$ 的有限元序数函数 $\overbrace{\text{Ord}→...→\text{Ord}}^n →A$, 记作 $A^{→n}$, 递归定义为

$$
\begin{aligned}
A^{→0} &:= A \\
A^{→n^+} &:= \text{Ord} → A^{→n}
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

**定义** 对 $n$ 元函数 $F : A^{→n}$ 的参数全部填零所得到的 $A$ 的元素, 记作 $F\kern{0.17em}\overset{.}{0} : A$, 递归定义为

$$
\begin{aligned}
(F : A^{→0})\kern{0.17em}\overset{.}{0} &:= F:A \\
(F : A^{→n^+})\kern{0.17em}\overset{.}{0} &:= (F\kern{0.17em}0 : A^{→n})\kern{0.17em}\overset{.}{0}
\end{aligned}
$$

```agda
_0̇ : A →ⁿ n → A
_0̇ {n = zero} = id
_0̇ {n = suc n} F = F 0 0̇
```

有时候我们想要留最后一位不填或最后两位不填.

**定义** 对 $n^+$ 元函数 $F : A^{→n^+}$ 的参数留最后一位不填, 其余全部填零, 所得到的函数记作 $F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} : \text{Ord}→A$, 递归定义为

$$
\begin{aligned}
(F : A^{→1})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} &:= F:\text{Ord}→A \\
(F : A^{→n^{++}})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} &:= (F\kern{0.17em}0 : A^{→n^+})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}
\end{aligned}
$$

```agda
_0̇,_ : A →ⁿ (suc n) → A →ⁿ 1
_0̇,_ {n = zero} = id
_0̇,_ {n = suc n} F = F 0 0̇,_
```

**定义** 对 $n^{++}$ 元函数 $F : A^{→n^{++}}$ 的参数留最后两位不填, 其余全部填零, 所得到的函数记作 $F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}\kern{0.17em}\underline{\kern{0.5em}} : \text{Ord}→\text{Ord}→A$, 递归定义为

$$
\begin{aligned}
(F : A^{→2})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}\kern{0.17em}\underline{\kern{0.5em}} &:= F:\text{Ord}→\text{Ord}→A \\
(F : A^{→n^{+++}})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}\kern{0.17em}\underline{\kern{0.5em}} &:= (F\kern{0.17em}0 : A^{→n^{++}})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}\kern{0.17em}\underline{\kern{0.5em}}
\end{aligned}
$$

```agda
_0̇,_,_ : A →ⁿ (2+ n) → A →ⁿ 2
_0̇,_,_ {n = zero} = id
_0̇,_,_ {n = suc n} F = F 0 0̇,_,_
```

**引理** 对 $n^+$ 元函数 $F : A^{→n^+}$, 第一位先填零, 剩余再全部填零, 或者除最后一位外全部填零, 然后最后一位再填零, 这两种做法都等于一开始就全部填零.

$$
\begin{aligned}
(F : A^{→n^+})\kern{0.17em}\overset{.}{0} &= (F\kern{0.17em}0: A^{→n})\kern{0.17em}\overset{.}{0} \\
(F : A^{→n^+})\kern{0.17em}\overset{.}{0} &= (F\kern{0.17em}\overset{.}{0}:A^{→1})\kern{0.17em}0
\end{aligned}
$$

```agda
0,0̇ : {F : A →ⁿ (suc n)} → F 0 0̇ ≡ F 0̇
0,0̇ = refl

0̇,0 : {F : A →ⁿ (suc n)} → F 0̇, 0 ≡ F 0̇
0̇,0 {n = zero} = refl
0̇,0 {n = suc _} {F} = 0̇,0 {F = F 0}
```

## 有限元Veblen函数

有了以上准备, 终于可以定义有限元Veblen函数了. 回想前篇的辅助函数 $\Phi$, 我们讲了它的二元, 三元和四元版本. 用下标表示元数, 再次列出它们的类型如下.

- $Φ_2:(\text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_3:(\text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_4:(\text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- ...

自然地推广下去, 用上一节刚定义的符号, 并且让下标从零开始, 我们现在需要定义一个

$$
Φ_n : \text{Ord}^{→n^+} → \text{Ord}^{→n^{++}}
$$

```agda
Φₙ : Ord →ⁿ suc n → Ord →ⁿ 2+ n
```

回顾不动点的起点 (梦的开始) $λα,ω\kern{0.17em}^α : \text{Ord}^{→1}$, 我们需要从它开始, 迭代 $Φ_{\lt n}$, 以得到 $Φ_n$. 直观上该迭代具有

$$
Φ_{n-1} (... (Φ_2 (Φ_1 (Φ_0 (λα,ω\kern{0.17em}^α))))...) : \text{Ord}^{→n^+}\quad (*)
$$

的形式. 我们把这整个迭代过程记作 $Φ$, 它具有类型

$$
Φ : \text{Ord}^{→1} → \prod_{n:ℕ}\text{Ord}^{→n^+}
$$

```agda
Φ : Ord →ⁿ 1 → (∀ n → Ord →ⁿ suc n)
```

非形式地, 简洁起见, 我们将把 $Φ\kern{0.17em}F\kern{0.17em}n$ 写作 $Φ^n\kern{0.17em}F$.

注意到 $Φ_n$ 的定义里就要用到 $(*)$ 式, 即 $Φ$ 的定义. 而 $Φ$ 的定义里又要用到每个 $Φ_{\lt n}$. 我们把它们写成互递归的形式, 也就是说同时定义 $Φ_n$ 和 $Φ$.

**定义** $Φ_n$ 和 $Φ$ 互递归定义如下.

$$
\begin{aligned}
&Φ_n\kern{0.17em}F :\text{Ord}^{→n^{++}} &:=& \text{rec}\kern{0.17em}F \\
&&&\quad (λ(φ_{n^+,α}:\text{Ord}^{→n^+}),Φ^n\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{n^+,α}\kern{0.17em}β\kern{0.17em}\overset{.}{0})) \\
&&&\quad (λ(φ_{n^+,f\kern{0.17em}m}:ℕ→\text{Ord}^{→n^+}), Φ^n\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+,f\kern{0.17em}m}\kern{0.17em}β\kern{0.17em}\overset{.}{0})) \\
\\
&Φ^0\kern{0.17em}F : \text{Ord}^{→1} &:=& F \\
&Φ^{n^+}\kern{0.17em}F : \text{Ord}^{→n^{++}} &:=& Φ_n\kern{0.17em}(Φ^n\kern{0.17em}F)
\end{aligned}
$$

```agda
-- 我们会给元数参数加一层括弧以方便辨认, 它们相当于 Φ 的上标.
Φₙ {n} F = rec F
  (λ φ-α  → Φ (fixpt λ β → φ-α β 0̇) (n))
  (λ φ[_] → Φ (jump λ β → lim λ m → φ[ m ] β 0̇) (n))

Φ F (zero) = F
Φ F ((suc n)) = Φₙ (Φ F (n))
```

**注意** 也可以不用互递归, 非形式地采用如下定义.

$$
\begin{aligned}
Φ_n\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_{n^+,α},Φ_{n-1} (... (Φ_2 (Φ_1 (Φ_0(\text{fixpt}\kern{0.17em}λβ,φ_{n^+,α}\kern{0.17em}β\kern{0.17em}\overset{.}{0}))))...)) \\
&(λφ_{n^+,f\kern{0.17em}m}, Φ_{n-1} (... (Φ_2 (Φ_1 (Φ_0(\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+,f\kern{0.17em}m}\kern{0.17em}β\kern{0.17em}\overset{.}{0}))))...))
\end{aligned}
$$

形式地, 可以把省略号换成自然数版本的 $\text{ind}$, 这里不展开讲解.

**定义** 有限元Veblen函数

$$
φ : \prod_{n:ℕ}\text{Ord}^{→n^{+}} := Φ\kern{0.17em}(λα,ω\kern{0.17em}^α)
$$

```agda
φ : ∀ n → Ord →ⁿ suc n
φ = Φ (ω ^_)
```

**事实** $n^{++}$ 元Veblen函数 $φ_{n^+}$ 等于对 $n^+$ 元Veblen函数 $φ_n$ 做一次 $Φ_n$, 并且首位输入零的话就等于 $φ_n$.

$$
\begin{aligned}
φ_{n^+} &= Φ_n\kern{0.17em}φ_n \\
φ_{n^+} 0 &= φ_n
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
φ_0 &= λα,ω^α \\
φ_1 &= \text{Bin}.φ \\
φ_2 &= \text{Tri}.φ \\
φ_3 &= \text{Qua}.φ
\end{aligned}
$$

```agda
φ₀ : φ (0) ≡ ω ^_
φ₀ = refl

φ₁ : φ (1) ≡ Bin.φ
φ₁ = refl

φ₂ : φ (2) ≡ Tri.φ
φ₂ = refl

φ₃ : φ (3) ≡ Qua.φ
φ₃ = refl
```

## 计算模式

回想四元Veblen函数的计算模式.

$$
\begin{aligned}
&Φ\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0\kern{0.17em}0\kern{0.17em}0 &=& (λβ,Φ\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}0\kern{0.17em}0)^ω\kern{0.17em}0 \\
&Φ\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0\kern{0.17em}0\kern{0.17em}β^+ &=& (λβ,Φ\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}0\kern{0.17em}0)^ω\kern{0.17em}(Φ\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}0\kern{0.17em}0\kern{0.17em}β)^+ \\
&Φ\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0\kern{0.17em}0\kern{0.17em}0 &=& \lim λn,Φ\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)\kern{0.17em}0\kern{0.17em}0\kern{0.17em}0 \\
&Φ\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0\kern{0.17em}0\kern{0.17em}β^+ &=& \lim λn,Φ\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)\kern{0.17em}(Φ\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}0\kern{0.17em}0\kern{0.17em}β)^+\kern{0.17em}0\kern{0.17em}0 \\
&Φ\kern{0.17em}F\kern{0.17em}α\kern{0.17em}0\kern{0.17em}0\kern{0.17em}(\lim g) &=& \lim λn,Φ\kern{0.17em}F\kern{0.17em}α\kern{0.17em}0\kern{0.17em}0\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

自然推广下去, 对于 $n$ 元, 系统地, 可以通过如下方法考察计算模式. 设

- $\mathcal{S}$ 表示任意参数序列
- $\mathcal{Z}$ 表示不特定多个零 (可能一个零都没有)
- $\mathcal{z,s,l}$ 分别表示单个零, 后继, 极限
- $\mathcal{α,β}$ 表示任意单个参数

那么所有参数模式都可匹配到 $(\mathcal{S,α,Z,β})$ 的模式, 且五大模式表示为

- $(\mathcal{S,s,Z,z})$
- $(\mathcal{S,s,Z,s})$
- $(\mathcal{S,l,Z,z})$
- $(\mathcal{S,l,Z,s})$
- $(\mathcal{S,α,Z,l})$

但 Agda 无法直接像四元那样直接证出这些模式, 因为卡在了下述引理, 它的证明需要归纳元数 $n$.

**引理** $(\mathcal{S,Z,α})$

$$
Φ^n\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} = F
$$

**(证明)** 归纳 $n$ 即得. ∎

```agda
Φ-ż-α : Φ F (n) 0̇,_ ≡ F
Φ-ż-α {n = zero} = refl
Φ-ż-α {n = suc n} = Φ-ż-α {n = n}
{-# REWRITE Φ-ż-α #-}
```

将该引理声明为新的重写规则, 可以立即证明:

**定理** 计算模式

$$
\begin{aligned}
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0} &=& (λβ,Φ^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}0 \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+ &=& (λβ,Φ^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}(Φ^{n^+}\kern{0.17em}F\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+ \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0} &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}\overset{.}{0} \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}β^+ &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}(Φ^{n^+}\kern{0.17em}F\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}β)^+\kern{0.17em}\overset{.}{0} \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g) &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}α\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}m)
\end{aligned}
$$

其中第五条要求前提 $F\kern{0.17em}(\lim g) = \lim λm,F\kern{0.17em}(g\kern{0.17em}m)$.

```agda
Φ-s-ż-z : Φ F ((suc n)) (suc α) 0̇, 0 ≡ iterω (λ β → Φ F (_) α β 0̇) 0
Φ-s-ż-z = refl

Φ-s-ż-s : Φ F ((suc n)) (suc α) 0̇, suc β ≡ iterω (λ β → Φ F (_) α β 0̇) (suc (Φ F (_) (suc α) 0̇, β))
Φ-s-ż-s = refl

Φ-l-ż-z : Φ F ((suc n)) (lim f) 0̇, 0 ≡ lim λ m → Φ F ((suc n)) (f m) 0̇
Φ-l-ż-z = refl

Φ-l-ż-s : Φ F ((suc n)) (lim f) 0̇, suc β ≡ lim λ m → Φ F (_) (f m) (suc (Φ F (_) (lim f) 0̇, β)) 0̇
Φ-l-ż-s = refl

Φ-α-ż-l : F (lim g) ≡ lim (λ m → F (g m))
  → Φ F ((suc n)) α 0̇, lim g ≡ lim λ m → Φ F ((suc n)) α 0̇, g m
Φ-α-ż-l {α = zero} = id
Φ-α-ż-l {α = suc _} _ = refl
Φ-α-ż-l {α = lim _} _ = refl
```

**推论** $(\mathcal{α,s,Z,β})$

$$
φ_{n^{++}}\kern{0.17em}α\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}=
\text{fixpt}\kern{0.17em}λγ,φ_{n^{++}}\kern{0.17em}α\kern{0.17em}β\kern{0.17em}γ\kern{0.17em}\overset{.}{0}
$$

**(证明)** 讨论 $α$, 由定理 $(\mathcal{S,Z,α})$ 即得. ∎

```agda
φ-α-s-ż-β : φ ((2+ n)) α (suc β) 0̇,_ ≡ fixpt λ γ → φ ((2+ n)) α β γ 0̇
φ-α-s-ż-β {n = zero} {α = zero} = refl
φ-α-s-ż-β {n = zero} {α = suc _} = refl
φ-α-s-ż-β {n = zero} {α = lim _} = refl
φ-α-s-ż-β {n = suc n} {α = zero} = Φ-ż-α
φ-α-s-ż-β {n = suc n} {α = suc _} = Φ-ż-α
φ-α-s-ż-β {n = suc n} {α = lim _} = Φ-ż-α
```

**推论** $(\mathcal{α,l,Z,β})$

$$
φ_{n^{++}}\kern{0.17em}α\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}=
\text{jump}\kern{0.17em}λδ,\limλm,φ_{n^{++}}\kern{0.17em}α\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}δ\kern{0.17em}\overset{.}{0}
$$

**(证明)** 讨论 $α$, 由定理 $(\mathcal{S,Z,α})$ 即得. ∎

```agda
φ-α-l-ż-β : φ ((2+ n)) α (lim f) 0̇,_ ≡ jump λ δ → lim λ m → φ ((2+ n)) α (f m) δ 0̇
φ-α-l-ż-β {n = zero} {α = zero} = refl
φ-α-l-ż-β {n = zero} {α = suc _} = refl
φ-α-l-ż-β {n = zero} {α = lim _} = refl
φ-α-l-ż-β {n = suc n} {α = zero} = Φ-ż-α
φ-α-l-ż-β {n = suc n} {α = suc _} = Φ-ż-α
φ-α-l-ż-β {n = suc n} {α = lim _} = Φ-ż-α
```

**推论** $(\mathcal{α,Z,l})$

$$
φ_{n^{++}}\kern{0.17em}α\kern{0.17em}0\kern{0.17em}(\lim g)=\limλm,φ_{n^{++}}\kern{0.17em}α\kern{0.17em}0\kern{0.17em}(g\kern{0.17em}m)
$$

**(证明)** 由定理 $(\mathcal{S,α,Z,l})$ 即得. ∎

```agda
φ-α-ż-l : φ ((2+ n)) α 0̇, lim g ≡ lim λ m → φ ((2+ n)) α 0̇, g m
φ-α-ż-l = Φ-α-ż-l refl
```

类似 $(\mathcal{S,Z,α})$, 我们还可以有

**引理** $(\mathcal{S,Z,α,β})$

$$
Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}\kern{0.17em}\underline{\kern{0.5em}} = Φ^{1}\kern{0.17em}F
$$

**(证明)** 归纳 $n$ 即得. ∎

```agda
Φ-ż-α-β : Φ F ((suc n)) 0̇,_,_ ≡ Φ F (1)
Φ-ż-α-β {n = zero} = refl
Φ-ż-α-β {n = suc n} = Φ-ż-α-β {n = n}
{-# REWRITE Φ-ż-α-β #-}
```

**定理** 计算模式

$$
\begin{aligned}
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α^+\kern{0.17em}\overset{.}{0} &=& (Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α\kern{0.17em}\underline{\kern{0.5em}})^ω\kern{0.17em}0 \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α^+\kern{0.17em}β^+ &=& (Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α\kern{0.17em}\underline{\kern{0.5em}})^ω\kern{0.17em}(Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α^+\kern{0.17em}β)^+ \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim f)\kern{0.17em}0 &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}0 \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim f)\kern{0.17em}β^+ &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}(Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim f)\kern{0.17em}β)^+ \\
&Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α\kern{0.17em}(\lim g) &=& \lim λm,Φ^{n^+}\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}α\kern{0.17em}(g\kern{0.17em}m)
\end{aligned}
$$

其中第五条要求前提 $F\kern{0.17em}(\lim g) = \lim λm,F\kern{0.17em}(g\kern{0.17em}m)$.

```agda
Φ-ż-s-0 : Φ F ((suc n)) 0̇, suc α , 0 ≡ iterω (Φ F ((suc n)) 0̇, α ,_) 0
Φ-ż-s-0 = refl

Φ-ż-s-s : Φ F ((suc n)) 0̇, suc α , suc β ≡ iterω (Φ F ((suc n)) 0̇, α ,_) (suc (Φ F ((suc n)) 0̇, (suc α) , β))
Φ-ż-s-s = refl

Φ-ż-l-0 : Φ F ((suc n)) 0̇, lim f , 0 ≡ lim λ m → Φ F ((suc n)) 0̇, f m , 0
Φ-ż-l-0 = refl

Φ-ż-l-s : Φ F ((suc n)) 0̇, lim f , suc β ≡ lim λ m → Φ F ((suc n)) 0̇, f m , suc (Φ F ((suc n)) 0̇, (lim f) , β)
Φ-ż-l-s = refl

Φ-ż-α-l : F (lim g) ≡ lim (λ m → F (g m))
  → Φ F ((suc n)) 0̇, α , lim g ≡ lim λ m → Φ F ((suc n)) 0̇, α , g m
Φ-ż-α-l {α = zero} = id
Φ-ż-α-l {α = suc _} _ = refl
Φ-ż-α-l {α = lim _} _ = refl
```

## SVO

**定义** 有限元Veblen序数的能力极限叫做 SVO (~~Subject–Verb–Object~~(不是) Small Veblen Ordinal).

$$
\begin{aligned}
\text{SVO} := &\lim λ n,φ_n\kern{0.17em}1\kern{0.17em}\overset{.}{0} \\
= &\lim\kern{0.17em}(φ_0(1),φ_1(1,0),φ_2(1,0,0),...)
\end{aligned}
$$

```agda
SVO : Ord
SVO = lim λ n → φ (n) 1 0̇
```

一个很大的大数:

$$
\text{svo}_{99}:=f_\text{SVO}(99)
$$

```agda
svo₉₉ = FGH.f SVO 99
```
