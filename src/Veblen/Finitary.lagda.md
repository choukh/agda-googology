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
0,0̇ : {F : A →ⁿ (suc n)} → F 0̇ ≡ F 0 0̇
0,0̇ = refl

0̇,0 : {F : A →ⁿ (suc n)} → F 0̇ ≡ F 0̇, 0
0̇,0 {n = zero} = refl
0̇,0 {n = suc _} {F} = 0̇,0 {F = F 0}
```

## 有限元Veblen函数

有了以上准备, 终于可以定义有限元Veblen函数了. 回想前篇的辅助函数 $\Phi$, 我们讲了它的二元, 三元和四元版本. 今后我们用下标表示元数, 再次列出它们的类型如下.

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

的形式. 我们把这整个迭代过程记作 $Φ^n$, 它具有类型

$$
Φ^n : \text{Ord}^{→1} → \text{Ord}^{→n^+}
$$

```agda
Φⁿ : Ord →ⁿ 1 → Ord →ⁿ suc n
```

注意到 $Φ_n$ 的定义里就要用到 $(*)$ 式, 即 $Φ^n$. 而 $Φ^n$ 的定义里又要用到每个 $Φ_{\lt n}$. 我们把它们写成互递归的形式, 也就是说同时定义 $Φ_n$ 和 $Φ^n$.

**定义** $Φ_n$ 和 $Φ^n$ 互递归定义如下.

$$
\begin{aligned}
Φ_n\kern{0.17em}F :\text{Ord}^{→n^{++}} &:= \text{rec}\kern{0.17em}F \\
&\qquad (λ(φ_{n^+,α}:\text{Ord}^{→n^+}),Φ^n(\text{fixpt}\kern{0.17em}λβ,φ_{n^+,α}\kern{0.17em}β\kern{0.17em}\overset{.}{0})) \\
&\qquad (λ(φ_{n^+,f\kern{0.17em}m}:ℕ→\text{Ord}^{→n^+}), Φ^n(\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+,f\kern{0.17em}m}[m]\kern{0.17em}β\kern{0.17em}\overset{.}{0})) \\
\\
Φ^0 : \text{Ord}^{→1}→\text{Ord}^{→1} &:= \text{id} \\
Φ^{n^+}\kern{0.17em}F : \text{Ord}^{→n^{++}} &:= Φ_n(Φ^n\kern{0.17em}F)
\end{aligned}
$$

```agda
Φₙ F = rec F
  (λ φ-α  → Φⁿ $ fixpt λ β → φ-α β 0̇)
  (λ φ[_] → Φⁿ $ jump λ β → lim λ n → φ[ n ] β 0̇)

Φⁿ {n = zero} = id
Φⁿ {n = suc n} F = Φₙ (Φⁿ F)
```

**注意** 也可以不用互递归, 非形式地采用如下定义.

$$
\begin{aligned}
Φ_n\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_{n^+,α},Φ_{n-1} (... (Φ_2 (Φ_1 (Φ_0(\text{fixpt}\kern{0.17em}λβ,φ_{n^+,α}\kern{0.17em}β\kern{0.17em}\overset{.}{0}))))...)) \\
&(λφ_{n^+,f\kern{0.17em}m}, Φ_{n-1} (... (Φ_2 (Φ_1 (Φ_0(\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+,f\kern{0.17em}m}[m]\kern{0.17em}β\kern{0.17em}\overset{.}{0}))))...))
\end{aligned}
$$

形式地, 可以把省略号换成自然数版本的 $\text{ind}$.

**定义** 有限元Veblen函数

$$
φ_n : \text{Ord}^{→n^{+}} := Φ^n(λα,ω\kern{0.17em}^α)
$$

```agda
φ : Ord →ⁿ suc n
φ = Φⁿ (ω ^_)
```

**事实** $n^{++}$ 元Veblen函数 $φ_{n^+}$ 等于对 $n^+$ 元Veblen函数 $φ_n$ 做一次 $Φ_n$, 并且首位输入零的话就等于 $φ_n$.

$$
\begin{aligned}
φ_{n^+} &= Φ_n\kern{0.17em}φ_n \\
φ_{n^+} 0 &= φ_n
\end{aligned}
$$

```agda
Φ-φ : φ {suc n} ≡ Φₙ (φ {n})
Φ-φ = refl

φ-0 : φ {suc n} 0 ≡ φ {n}
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

如果说三元或四元的时候我们还可以穷举各个参数分别为零, 后继, 极限的情况, $n$ 元的时候就不可能了, 但我们可以通过如下方法来把握.

我们设

- $\mathcal{Z}$ 表示不特定多个零
- $\mathcal{X}$ 表示不特定多个非零
- $\mathcal{xZy}$ 表示零和非零的混合, 但首尾非零
- $\mathcal{z,s,l,x}$ 分别表示单个零, 后继, 极限, 非零参数

那么所有参数模式都可匹配到 $(\mathcal{Z,xZy,Z,X})$. 最前面的 $\mathcal{Z}$ 不起任何作用, 可以直接忽略, 于是我们只需讨论 $(\mathcal{xZy,Z,X})$ 的模式, 而这种模式很方便写成定理. 具体地, 我们考察以下模式.

- $(\mathcal{s,Z,x})$
- $(\mathcal{l,Z,x})$
  - $(\mathcal{l,Z,z})$
  - $(\mathcal{l,Z,s})$
  - $(\mathcal{l,Z,l})$
- $(\mathcal{x,s,Z,y})$
- $(\mathcal{x,l,Z,y})$
- $(\mathcal{x,Z,s,y})$
- $(\mathcal{x,Z,l,y})$

**引理** $(\mathcal{Z,x})$

$$
Φ^n\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} = F
$$

**(证明)** 归纳 $n$ 即得. ∎

```agda
Φ-ż-x : Φⁿ {n} F 0̇,_ ≡ F
Φ-ż-x {n = zero} = refl
Φ-ż-x {n = suc n} = Φ-ż-x {n}
```

**定理** $(\mathcal{s,Z,x})$

$$
φ_{n^+}\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}=
\text{fixpt}\kern{0.17em}λβ,φ_{n^+}\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0}
$$

**(证明)** 依定义

$$
\begin{aligned}
φ_{n^+}\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}
&=
Φ_n\kern{0.17em}φ_n\kern{0.17em}α^+\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} \\
&=
Φ^n\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{n^+}\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0})\kern{0.17em}\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} \\
&=
\text{fixpt}\kern{0.17em}λβ,φ_{n^+}\kern{0.17em}α\kern{0.17em}β\kern{0.17em}\overset{.}{0}
\end{aligned}
$$

其中第三个等号用了引理 $(\mathcal{Z,x})$. ∎

```agda
φ-s-ż-x : φ {suc n} (suc α) 0̇,_ ≡ fixpt λ β → φ α β 0̇
φ-s-ż-x {n} {α} = begin
  φ {suc n} (suc α) 0̇,_         ≡⟨⟩
  Φₙ (φ {n}) (suc α) 0̇,_        ≡⟨⟩
  Φⁿ (fixpt λ β → φ α β 0̇) 0̇,_  ≡⟨ Φ-ż-x ⟩
  fixpt (λ β → φ α β 0̇)         ∎
```

**定理** $(\mathcal{l,Z,x})$

$$
φ_{n^+}\kern{0.17em}(\lim f)\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}=
\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+}\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}β\kern{0.17em}\overset{.}{0}
$$

**(证明)** 依定义

$$
\begin{aligned}
φ_{n^+}\kern{0.17em}(\lim f)\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}}
&=
Φ_n\kern{0.17em}φ_n\kern{0.17em}(\lim f)\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} \\
&=
Φ^n\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+}\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}β\kern{0.17em}\overset{.}{0})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} \\
&=
\text{jump}\kern{0.17em}λβ,\limλm,φ_{n^+}\kern{0.17em}(f\kern{0.17em}m)\kern{0.17em}β\kern{0.17em}\overset{.}{0}
\end{aligned}
$$

其中第三个等号用了引理 $(\mathcal{Z,x})$. ∎

```agda
φ-l-ż-x : φ {suc n} (lim f) 0̇,_ ≡ jump λ β → lim λ m → φ {suc n} (f m) β 0̇
φ-l-ż-x {n} {f} = begin
  φ {suc n} (lim f) 0̇,_                     ≡⟨⟩
  Φₙ (φ {n}) (lim f) 0̇,_                    ≡⟨⟩
  Φⁿ (jump λ β → lim λ m → φ (f m) β 0̇) 0̇,_ ≡⟨ Φ-ż-x ⟩
  jump (λ β → lim λ m → φ (f m) β 0̇)        ∎
```

回想二元Veblen函数的计算式

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}0 &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(β^+) &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}(\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}β)^+ \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(\text{lim}\kern{0.17em}g) &= \text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f}\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

对有限元Veblen函数我们有类似的以下三个推论.

**推论** $(\mathcal{l,Z,z})$

```agda
φ-l-ż-z : φ {n} (lim f) 0̇ ≡ lim λ m → φ {n} (f m) 0̇
φ-l-ż-z {n = zero} = refl
φ-l-ż-z {n = suc n} {f} = begin
  φ {suc n} (lim f) 0 0̇                         ≡⟨ 0̇,0 ⟩
  φ {suc n} (lim f) 0̇, 0                        ≡⟨ cong-app φ-l-ż-x 0 ⟩
  jump (λ β → lim λ m → φ {suc n} (f m) β 0̇) 0  ≡⟨⟩
  lim (λ m → φ (f m) 0̇)                         ∎
```

**推论** $(\mathcal{l,Z,s})$

```agda
φ-l-ż-s : φ {suc n} (lim f) 0̇, (suc α) ≡ lim λ m → φ (f m) (suc (φ {suc n} (lim f) 0̇, α)) 0̇
φ-l-ż-s {n} {f} {α} =
  let j = jump λ β → lim λ m → φ (f m) β 0̇ in   begin
  φ {suc n} (lim f) 0̇, (suc α)                  ≡⟨ cong-app φ-l-ż-x (suc α) ⟩
  j (suc α)                                     ≡⟨⟩
  lim (λ m → φ (f m) (suc (j α)) 0̇)             ≡˘⟨
    cong (λ x → lim (λ m → φ {suc n} (f m) (suc (x α)) 0̇)) φ-l-ż-x ⟩
  lim (λ m → φ (f m) (suc (φ (lim f) 0̇, α)) 0̇)  ∎
```

**推论** $(\mathcal{l,Z,l})$

```agda
φ-l-ż-l : φ {suc n} (lim f) 0̇, (lim g) ≡ lim λ m → φ (lim f) 0̇, (g m)
φ-l-ż-l {n} {f} {g} =
  let j = jump λ β → lim λ m → φ (f m) β 0̇ in begin
  φ {suc n} (lim f) 0̇, (lim g)                ≡⟨ cong-app φ-l-ż-x (lim g) ⟩
  j (lim g)                                   ≡⟨⟩
  lim (λ m → j (g m))                         ≡˘⟨ cong (λ x → lim (λ m → x (g m))) φ-l-ż-x ⟩
  lim (λ m → φ (lim f) 0̇, (g m))              ∎
```

**定理**

```agda
φ-x-s-ż-y : φ {2+ n} α (suc β) 0̇,_ ≡ fixpt λ γ → φ {2+ n} α β γ 0̇
φ-x-s-ż-y {n = zero} {α = zero} = refl
φ-x-s-ż-y {n = zero} {α = suc _} = refl
φ-x-s-ż-y {n = zero} {α = lim _} = refl
φ-x-s-ż-y {n = suc n} {α = zero} = Φ-ż-x
φ-x-s-ż-y {n = suc n} {α = suc _} = Φ-ż-x
φ-x-s-ż-y {n = suc n} {α = lim _} = Φ-ż-x

φ-x-l-ż-y : φ {2+ n} α (lim f) 0̇,_ ≡ jump λ δ → lim λ m → φ {2+ n} α (f m) δ 0̇
φ-x-l-ż-y {n = zero} {α = zero} = refl
φ-x-l-ż-y {n = zero} {α = suc _} = refl
φ-x-l-ż-y {n = zero} {α = lim _} = refl
φ-x-l-ż-y {n = suc n} {α = zero} = Φ-ż-x
φ-x-l-ż-y {n = suc n} {α = suc _} = Φ-ż-x
φ-x-l-ż-y {n = suc n} {α = lim _} = Φ-ż-x
```

**引理**

```agda
Φ-ż-s-x : Φⁿ {suc n} F 0̇, (suc α) ,_ ≡ fixpt (Φⁿ {suc n} F 0̇, α ,_)
Φ-ż-s-x {n = zero} = refl
Φ-ż-s-x {n = suc n} = Φ-ż-s-x {n}

Φ-ż-l-x : Φⁿ {suc n} F 0̇, (lim f) ,_ ≡ jump λ β → lim λ m → Φⁿ {suc n} F 0̇, (f m) , β
Φ-ż-l-x {n = zero} = refl
Φ-ż-l-x {n = suc n} = Φ-ż-l-x {n}
```

**定理**

```agda
φ-ż-s-x : φ {suc n} 0̇, (suc α) ,_ ≡ fixpt (φ {suc n} 0̇, α ,_)
φ-ż-s-x = Φ-ż-s-x

φ-ż-l-x : φ {suc n} 0̇, (lim f) ,_ ≡ jump λ β → lim λ m → φ {suc n} 0̇, (f m) , β
φ-ż-l-x = Φ-ż-l-x
```

**定理**

```agda
φ-x-ż-s-y : φ {2+ n} α 0̇, (suc β) ,_ ≡ fixpt (φ {2+ n} α 0̇, β ,_)
φ-x-ż-s-y {n = zero} {α = zero} = refl
φ-x-ż-s-y {n = zero} {α = suc _} = refl
φ-x-ż-s-y {n = zero} {α = lim _} = refl
φ-x-ż-s-y {n = suc n} {α = zero} = Φ-ż-s-x
φ-x-ż-s-y {n = suc n} {α = suc _} = Φ-ż-s-x
φ-x-ż-s-y {n = suc n} {α = lim _} = Φ-ż-s-x

φ-x-ż-l-y : φ {2+ n} α 0̇, (lim f) ,_ ≡ jump λ δ → lim λ m → φ {2+ n} α 0̇, (f m) , δ
φ-x-ż-l-y {n = zero} {α = zero} = refl
φ-x-ż-l-y {n = zero} {α = suc _} = refl
φ-x-ż-l-y {n = zero} {α = lim _} = refl
φ-x-ż-l-y {n = suc n} {α = zero} = Φ-ż-l-x
φ-x-ż-l-y {n = suc n} {α = suc _} = Φ-ż-l-x
φ-x-ż-l-y {n = suc n} {α = lim _} = Φ-ż-l-x
```

## SVO

**定义** 有限元Veblen序数的能力极限叫做 SVO (~~Subject–Verb–Object~~ Small Veblen Ordinal).

$$
\begin{aligned}
\text{SVO} := &\lim λ n,φ_n\kern{0.17em}1\kern{0.17em}\overset{.}{0} \\
= &\lim\kern{0.17em}(φ(1),φ(1,0),φ(1,0,0),...)
\end{aligned}
$$

```agda
SVO : Ord
SVO = lim λ n → φ {n} 1 0̇
```

一个很大的大数:

$$
\text{svo}_{99}:=f_\text{SVO}(99)
$$

```agda
svo₉₉ = FGH.f SVO 99
```
