---
title: 形式化大数数学 (1.4 - 超限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/707713300
---

# 形式化大数数学 (1.4 - 超限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Transfinitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Transfinitary.lagda.md)  
> 高亮渲染: [Transfinitary.html](https://choukh.github.io/agda-googology/Veblen.Transfinitary.html)  

本篇我们来定义超限元Veblen函数, 也叫序元Veblen函数. 它在形式上只依赖我们的第一篇: [形式化大数数学 (1.0 - 序数, 增长层级, 不动点)](https://zhuanlan.zhihu.com/p/705306447). 在认知上是前几篇的自然推广, 而没有什么非常新的东西. 所以我们会讲得很简洁, 如有疑问请参考前几篇.

Agda 编程上, 我们开启了一些高级特性 (有损合一化, 自定义重写), 它们只是为了让代码更简洁 (比非形式写法还简洁), 而不影响目标函数的性质以及证明的可靠性.

```agda
{-# OPTIONS --lossy-unification --rewriting --local-confluence-check #-}
module Veblen.Transfinitary where
open import Veblen.Base public
```

## 超限元函数类型

**定义** 递归定义超限元函数类型

$$
A^{→α} := \begin{cases}
A & \text{if } α = 0 \\
\text{Ord} → A^{→β} & \text{if } α = β^+ \\
\prod_n A^{→ (f\kern{0.17em}n)^+} & \text{if } α = \lim f
\end{cases}
$$

```agda
_→^_ : Set → Ord → Set
A →^ zero = A
A →^ suc α = Ord → A →^ α
A →^ lim f = ∀ {n} → Ord → A →^ f n
```

**约定** 对任意 $F : \text{Ord}^{→\lim f}$ 我们用下标表示 $F_n : \text{Ord}^{→(f\kern{0.17em}n)^+}$.

**注意** 上面的定义可以使用序数的递归原理 $\text{rec}$. 这里不使用的原因是没有必要. 之前使用的唯一原因是方便证明推广后的函数确实具有与推广前的函数相等的部分——两个递归函数只有归约到相同的 $\text{rec}$ 形式 Agda 才认为定义相等 (definitional equality), 否则依赖函数外延性 (functional extensionality). 这里我们是从自然数元推广到序数元, 怎样都无法证明定义相等.

**定义** 给一个超限元函数的参数全部填零的高阶函数

$$
λF,F\kern{0.17em}\overset{.}{0} : A^{→α} → A
$$

定义为

$$
(F : A^{→α})\kern{0.17em}\overset{.}{0} := \begin{cases}
F:A & \text{if } α = 0 \\
(F\kern{0.17em}0 : A^{→β})\kern{0.17em}\overset{.}{0} & \text{if } α = β^+ \\
(F_0\kern{0.17em}0 : A^{→f\kern{0.17em}0})\kern{0.17em}\overset{.}{0} & \text{if } α = \lim f
\end{cases}
$$

```agda
_0̇ : A →^ α → A
_0̇ {α = zero} = id
_0̇ {α = suc _} F = F 0 0̇
_0̇ {α = lim _} F = F {0} 0 0̇
```

**定义** 给一个超限元函数的参数除最后一位外全部填零的高阶函数

$$
λF,F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} : A^{→α^+} → A^{→1}
$$

定义为

$$
(F : A^{→α^+})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} := \begin{cases}
F:A^{→1} & \text{if } α = 0 \\
(F\kern{0.17em}0 : A^{→β^+})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} & \text{if } α = β^+ \\
((F\kern{0.17em}0)_0 : A^{→(f\kern{0.17em}0)^+})\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} & \text{if } α = \lim f
\end{cases}
$$

```agda
_0̇,_ : A →^ suc α → A →^ 1
_0̇,_ {α = zero} = id
_0̇,_ {α = suc _} F = F 0 0̇,_
_0̇,_ {α = lim _} F = F 0 {0} 0̇,_
```

## 超限元Veblen函数

**定义** 互递归定义以下3个辅助函数

- 后继元辅助函数 $Φ_{α^+} : \text{Ord}^{→α^+} → \text{Ord}^{→α^{++}}$
- 极限元辅助函数 $Φ_{\lim f} : \text{Ord}^{→\lim f} → \text{Ord}^{→(f\kern{0.17em}n)^+}$
  - 即 $(\prod_n \text{Ord}^{→(f\kern{0.17em}n)^+}) → \text{Ord}^{→(f\kern{0.17em}n)^+}$
- $α$ 元辅助函数 $Φ^{α} : \text{Ord}^{→1} → \prod_α \text{Ord}^{→α^+}$

```agda
Φₛ : Ord →^ suc α → Ord →^ 2+ α
Φₗ : Ord →^ lim f → Ord →^ suc (lim f)
Φ : Ord →^ 1 → (∀ {α} → Ord →^ suc α)
```

$$
\begin{aligned}
Φ_{α^+}\kern{0.17em}F &:= \text{rec}\kern{0.17em}F \\
&\quad (λ φ_{α^+,β}, Φ^{α}\kern{0.17em}(\text{fixpt}\kern{0.17em}(λγ,φ_{α^+,β}\kern{0.17em}γ\kern{0.17em}\overset{.}{0}))) \\
&\quad (λ φ_{α^+,g\kern{0.17em}n}, Φ^{α}\kern{0.17em}(\text{jump}\kern{0.17em}(λγ,\lim λ n,φ_{α^+,g\kern{0.17em}n}\kern{0.17em}γ\kern{0.17em}\overset{.}{0}))) \\
\end{aligned}
$$

```agda
Φₛ F = rec F
  (λ φ → Φ $ fixpt λ γ → φ γ 0̇)
  (λ φ → Φ $ jump λ γ → lim λ n → φ n γ 0̇)
```

$$
\begin{aligned}
Φ_{\lim f}\kern{0.17em}F &:= \text{rec}\kern{0.17em}F \\
&\quad (λ φ_{\lim f,β} λn , Φ^{f\kern{0.17em}n}\kern{0.17em}(\text{jump}_1\kern{0.17em}(λγ,\lim λ m,φ_{\lim f,β,m}\kern{0.17em}γ\kern{0.17em}\overset{.}{0}))) \\
&\quad (λ φ_{\lim f,g\kern{0.17em}n} λn , Φ^{f\kern{0.17em}n}\kern{0.17em}(\text{jump}\kern{0.17em}(λγ,\lim λ m,φ_{\lim f,g\kern{0.17em}m,m}\kern{0.17em}γ\kern{0.17em}\overset{.}{0}))) \\
\end{aligned}
$$

```agda
Φₗ F = rec F
  (λ φ → Φ $ jump⟨ 1 ⟩ λ γ → lim λ n → φ {n} γ 0̇)
  (λ φ → Φ $ jump λ γ → lim λ n → φ n {n} γ 0̇)
```

$$
Φ^{α}\kern{0.17em}F := \begin{cases}
F & \text{if } α = 0 \\
Φ_{β^+}\kern{0.17em}(Φ^{β}\kern{0.17em}F) & \text{if } α = β^+ \\
Φ_{\lim f}\kern{0.17em}(λn,Φ^{f\kern{0.17em}n}\kern{0.17em}F) & \text{if } α = \lim f
\end{cases}
$$

```agda
Φ F {α = zero}  = F
Φ F {α = suc α} = Φₛ (Φ F)
Φ F {α = lim f} = Φₗ (Φ F)
```

**定义** 超限元Veblen函数

$$
φ_α := Φ^α\kern{0.17em}(λα,ω^α)
$$

```agda
φ : ∀ {α} → Ord →^ suc α
φ = Φ (ω ^_)
```

**例** 容易验证

$$
\begin{aligned}
φ_{0} &= \text{Fin.}φ\kern{0.17em}0 \\
φ_{1} &= \text{Fin.}φ\kern{0.17em}1 \\
φ_{2} &= \text{Fin.}φ\kern{0.17em}2 \\
\end{aligned}
$$

```agda
import Veblen.Finitary as Fin

φ₀ : φ {0} ≡ Fin.φ 0
φ₀ = refl

φ₁ : φ {1} ≡ Fin.φ 1
φ₁ = refl

φ₂ : φ {2} ≡ Fin.φ 2
φ₂ = refl
```

后文我们补上一种容易阅读的非形式记法——双行有限列矩阵: 第一行是所有非零参数, 第二行是参数的序号. 如 $φ_{2}\kern{0.17em}2\kern{0.17em}1\kern{0.17em}0$ 写作 $\begin{pmatrix}2&1\\2&1\end{pmatrix}$.

**引理** 右侧的零参数可以省去:

$$
Φ^α\kern{0.17em}F\kern{0.17em}\overset{.}{0}\kern{0.17em}\underline{\kern{0.5em}} = F
$$

即

$$
\begin{pmatrix}
...&0\\
...&α
\end{pmatrix}
=
\begin{pmatrix}
...\\
...
\end{pmatrix}
$$

```agda
Φ-ż-α : Φ F {α} 0̇,_ ≡ F
Φ-ż-α {α = zero} = refl
Φ-ż-α {α = suc α} = Φ-ż-α {α = α}
Φ-ż-α {α = lim f} = Φ-ż-α {α = f 0}
{-# REWRITE Φ-ż-α #-}
```

Agda 编程上, 我们将以上引理声明为新的重写规则, 以方便证明以下定理.

**定理** 计算模式 (后继元五条加极限元五条, 共十条)

$$
Φ^{α^+}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}0 = (λγ,Φ^{α^+}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}γ\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}0
$$

$$
\begin{pmatrix}
...&β^+\\
...&α^+
\end{pmatrix}
=
\begin{pmatrix}
...&β&λ\\
...&α^+&α
\end{pmatrix}^ω\kern{0.17em}0
=
\begin{pmatrix}
...&β&\begin{pmatrix}
...&β&_⋰\begin{pmatrix}
...&β&0\\
...&α^+&α
\end{pmatrix}\\
...&α^+&α
\end{pmatrix}\\
...&α^+&α
\end{pmatrix}
$$

```agda
Φₛ-s-ż-z : (Φ F {suc α} (suc β) 0̇, 0) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) 0
Φₛ-s-ż-z = refl
```

$$
Φ^{α^+}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}γ^+ = (λγ,Φ^{α^+}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}γ\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}(Φ^{α^+}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}γ)^+
$$

$$
\begin{pmatrix}
...&β^+&γ^+\\
...&α^+&0
\end{pmatrix}
=
\begin{pmatrix}
...&β&λ\\
...&α^+&α
\end{pmatrix}^ω\kern{0.17em}
\begin{pmatrix}
...&β^+&γ\\
...&α^+&0
\end{pmatrix}^+
$$

```agda
Φₛ-s-ż-s : (Φ F {suc α} (suc β) 0̇, suc γ) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) (suc (Φ F {suc α} (suc β) 0̇, γ))
Φₛ-s-ż-s = refl
```

$$
Φ^{α^+}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}0 = \lim λ n,Φ^{α^+}\kern{0.17em}F\kern{0.17em}(g\kern{0.17em}n)\kern{0.17em}0\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&\lim g\\
...&α^+
\end{pmatrix}
=
\lim λn,\begin{pmatrix}
...&g\kern{0.17em}n\\
...&α^+
\end{pmatrix}
$$

```agda
Φₛ-l-ż-z : (Φ F {suc α} (lim g) 0̇, 0) ≡ lim λ n → Φ F {suc α} (g n) 0 0̇
Φₛ-l-ż-z = refl
```

$$
Φ^{α^+}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}γ^+ = \lim λ n,Φ^{α^+}\kern{0.17em}F\kern{0.17em}(g\kern{0.17em}n)\kern{0.17em}(Φ^{α^+}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}γ)^+\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&\lim g&γ^+\\
...&α^+&0
\end{pmatrix}
=
\lim λn,\begin{pmatrix}
...&g\kern{0.17em}n&
  \begin{pmatrix}
  ...&\lim g&γ\\
  ...&α^+&0
  \end{pmatrix}^+\\
...&α^+&α
\end{pmatrix}
$$

```agda
Φₛ-l-ż-s : (Φ F {suc α} (lim g) 0̇, suc γ) ≡ lim λ n → Φ F {suc α} (g n) (suc (Φ F {suc α} (lim g) 0̇, γ)) 0̇
Φₛ-l-ż-s = refl
```

$$
Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}0
=
\lim λ n,(Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β)_n\kern{0.17em}1\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&β^+\\
...&\lim f
\end{pmatrix}
=
\lim λ n,\begin{pmatrix}
...&β&1\\
...&\lim f&f\kern{0.17em}n
\end{pmatrix}
$$

```agda
Φₗ-s-ż-z : Φ F {lim f} (suc β) {n} 0̇, 0 ≡ lim λ n → Φ F {lim f} β {n} 1 0̇
Φₗ-s-ż-z = refl
```

$$
Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}γ^+
=
\lim λ n,(Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β)_n\kern{0.17em}(Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β^+\kern{0.17em}\overset{.}{0}\kern{0.17em}γ)^+\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&β^+&γ^+\\
...&\lim f&0
\end{pmatrix}
=
\lim λ n,\begin{pmatrix}
...&β&
  \begin{pmatrix}
  ...&β^+&γ\\
  ...&\lim f&0
  \end{pmatrix}^+
\\
...&\lim f&f\kern{0.17em}n
\end{pmatrix}
$$

```agda
Φₗ-s-ż-s : Φ F {lim f} (suc β) {n} 0̇, suc γ ≡ lim λ n → Φ F {lim f} β {n} (suc (Φ F {lim f} (suc β) {n} 0̇, γ)) 0̇
Φₗ-s-ż-s = refl
```

$$
Φ^{\lim f}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}0
=
\lim λ n,Φ^{\lim f}\kern{0.17em}F\kern{0.17em}(g\kern{0.17em}n)\kern{0.17em}0\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&\lim g\\
...&\lim f
\end{pmatrix}
=
\lim λ n,\begin{pmatrix}
...&g\kern{0.17em}n\\
...&\lim f
\end{pmatrix}
$$

```agda
Φₗ-l-ż-z : Φ F {lim f} (lim g) {n} 0̇, 0 ≡ lim λ n → Φ F {lim f} (g n) {n} 0 0̇
Φₗ-l-ż-z = refl
```

$$
Φ^{\lim f}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}γ^+
=
\lim λ n,Φ^{\lim f}\kern{0.17em}F\kern{0.17em}(g\kern{0.17em}n)\kern{0.17em}(Φ^{\lim f}\kern{0.17em}F\kern{0.17em}(\lim g)\kern{0.17em}\overset{.}{0}\kern{0.17em}γ)^+\kern{0.17em}\overset{.}{0}
$$

$$
\begin{pmatrix}
...&\lim g&γ^+\\
...&\lim f&0
\end{pmatrix}
=
\lim λ n,\begin{pmatrix}
...&g\kern{0.17em}n&
  \begin{pmatrix}
  ...&\lim g&γ\\
  ...&\lim f&0
  \end{pmatrix}^+
\\
...&\lim f&f\kern{0.17em}n
\end{pmatrix}
$$

```agda
Φₗ-l-ż-s : Φ F {lim f} (lim g) {n} 0̇, suc γ ≡ lim λ n → Φ F {lim f} (g n) {n} (suc (Φ F {lim f} (lim g) {n} 0̇, γ)) 0̇
Φₗ-l-ż-s = refl
```

$$
Φ^{α^+}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
=
\lim λn,Φ^{α^+}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}n)
$$

$$
\begin{pmatrix}
...&β&\lim g\\
...&α^+&0
\end{pmatrix}
=
\lim λn,\begin{pmatrix}
...&β&g\kern{0.17em}n\\
...&α^+&0
\end{pmatrix}
$$

只要

$$
F\kern{0.17em}(\lim g) = \lim λ n,F\kern{0.17em}(g\kern{0.17em}n)
$$

```agda
Φₛ-β-ż-l : F (lim g) ≡ lim (λ n → F (g n))
  → (Φ F {suc α} β 0̇, lim g) ≡ lim λ n → Φ F {suc α} β 0̇, g n
Φₛ-β-ż-l {β = zero} = id
Φₛ-β-ż-l {β = suc _} _ = refl
Φₛ-β-ż-l {β = lim _} _ = refl
```

$$
Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}\overset{.}{0}\kern{0.17em}(\lim g)
=
\lim λn,Φ^{\lim f}\kern{0.17em}F\kern{0.17em}β\kern{0.17em}\overset{.}{0}\kern{0.17em}(g\kern{0.17em}n)
$$

$$
\begin{pmatrix}
...&β&\lim g\\
...&\lim f&0
\end{pmatrix}
=
\lim λn,\begin{pmatrix}
...&β&g\kern{0.17em}n\\
...&\lim f&0
\end{pmatrix}
$$

只要

$$
F\kern{0.17em}(\lim g) = \lim λ n,F\kern{0.17em}(g\kern{0.17em}n)
$$

```agda
Φₗ-β-ż-l : F (lim g) ≡ lim (λ n → F (g n))
  → (Φ F {lim f} β {n} 0̇, lim g) ≡ lim λ n → Φ F {lim f} β {n} 0̇, g n
Φₗ-β-ż-l {β = zero} = id
Φₗ-β-ż-l {β = suc _} _ = refl
Φₗ-β-ż-l {β = lim _} _ = refl
```

## LVO

**定义** Small Veblen Ordinal

$$
\text{SVO} := (φ_ω\kern{0.17em}1)_0\kern{0.17em}0 =
\begin{pmatrix}
1 \\
ω \\
\end{pmatrix}
$$

```agda
SVO : Ord
SVO = φ {ω} 1 {0} 0
```

**定义** Large Veblen Ordinal

$$
\text{LVO} := (λα,φ_α\kern{0.17em}1\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}0 =
\begin{pmatrix}
1 \\
\begin{pmatrix}
1 \\
\begin{pmatrix}
1 \\
... \\
\end{pmatrix} \\
\end{pmatrix} \\
\end{pmatrix}
$$

```agda
LVO : Ord
LVO = fixpt (λ α → φ {α} 1 0̇) 0
```

这是超限元Veblen函数的能力极限.

**例** 一个很大的大数

$$
\text{lvo}_{99} := f_{\text{LVO}}(99)
$$

```agda
lvo₉₉ : ℕ
lvo₉₉ = FGH.f LVO 99
```

如果仅仅是为了写出该数的定义, 省去一切讨论, 不超过100行代码就可以实现. 读者可以试着摘抄出一段最简代码.

没有什么阻止我们继续向上, 例如轻易地就可以有

**定义** 第二代超限元Veblen函数以及第二代LVO

$$
\begin{aligned}
\overset{.}{φ} &:= Φ\kern{0.17em}(\text{fixpt}λα,φ_α\kern{0.17em}1\kern{0.17em}\overset{.}{0}) \\
\text{LVO}_2 &:= (λα,\overset{.}{φ}_α\kern{0.17em}1\kern{0.17em}\overset{.}{0})^ω\kern{0.17em}0
\end{aligned}
$$

```agda
φ̇ : ∀ {α} → Ord →^ suc α
φ̇ = Φ (fixpt (λ α → φ {α} 1 0̇))

LVO₂ : Ord
LVO₂ = fixpt (λ α → φ̇ {α} 1 0̇) 0
```

但这个模式是重复的, 一般我们就此打住, 转而使用全新的更高级方法, 如序数崩塌函数 (Ordinal Collapsing Function, OCF). 这将开启我们的形式化大数数学 (2.x) 篇.
