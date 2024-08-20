---
title: 形式化大数数学 (2.2 - 序数算术)
zhihu-tags: Agda, 大数数学, 序数
zhihu-url: https://zhuanlan.zhihu.com/p/715504174
---

# 形式化大数数学 (2.2 - 序数算术)

> 交流Q群: 893531731  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-googology/WellFormed.Arithmetic.html)  

前两篇我们[定义了良构树序数](https://zhuanlan.zhihu.com/p/711649863)并[讨论了其性质](https://zhuanlan.zhihu.com/p/715404245). 本篇开始向大序数进发. 作为准备, 我们先建立基本的算术运算.

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Arithmetic where
open import WellFormed.Base
open import WellFormed.Properties
```

## 序数函数

先补充定义序数函数的一些性质. 我们用大写的 $F$ 表示序数函数.

```agda
private variable F : Func
```

**定义 2-2-0** 我们说一个序数函数 $F$ **膨胀**一个序数关系 $\sim$, 当且仅当对任意序数 $x$ 都有 $x \sim F(x)$.

```agda
_inflates_ : Func → Rel → Type
F inflates _~_ = ∀ {x} → x ~ F x
```

**事实 2-2-1** 如果 $F$ 膨胀 $\lt$, 那么 $F$ 膨胀 $\leq$.

```agda
map-infl≤ : F inflates _<_ → F inflates _≤_
map-infl≤ p = <→≤ p
```

**定义 2-2-2** 给定序数谓词 $P : \text{Pred}$, 我们把限制到 $P$ 上的序数函数记作 $F ↾ P$, 其类型记作 $\text{Func}↾P$.

```agda
Func↾ : Pred → Type
Func↾ P = (x : Ord) ⦃ p : P x ⦄ → Ord

_↾_ : Func → (P : Pred) → Func↾ P
F ↾ P = λ x → F x
```

扩展「保持」和「膨胀」的定义, 使得被限制的函数 $F ↾ P$ 也可以谈论保持和膨胀.

**定义 2-2-3** 我们说 $F$ 在 $P$ **之内**保持(或膨胀) $\sim$, 当且仅当 $F$ 在限制到 $P$ 后保持(或膨胀) $\sim$.

```agda
restricted-pres-syntax : {P : Pred} → Func↾ P → Rel → Type
restricted-pres-syntax {P} F _~_ = ∀ {x y} ⦃ p : P x ⦄ ⦃ q : P y ⦄ → x ~ y → F x ~ F y
syntax restricted-pres-syntax {P} F _~_ = F preserves _~_ within P

restricted-infl-syntax : {P : Pred} → Func↾ P → Rel → Type
restricted-infl-syntax {P} F _~_ = ∀ {x} ⦃ p : P x ⦄ → x ~ F x
syntax restricted-infl-syntax {P} F _~_ = F inflates _~_ within P
```

## 一些约定

**约定 2-2-4** 我们将 $\text{suc}(\text{suc}(a))$ 简记作 $a^{++}$.

```agda
pattern 2+ a = suc (suc a)
```

类似定义 2-1-7, 我们有

**定义 2-2-5** 非零序数谓词: 它仅在遇到零时为假. 该谓词是可判定的.

```agda
nonZero : Pred
nonZero zero = ⊥
nonZero _ = ⊤
```

该谓词将只作为一个守护条件, 而不参与运算的构造, 我们将它封装为证明无关的记录类型, 以方便证明运算的性质.

```agda
record NonZero (a : Ord) : Type where
  field .wrap : nonZero a
```

**事实 2-2-6** $a$ 非零与 $a > 0$ 等价.

```agda
nz-intro-rd : Road 0 a → NonZero a
nz-intro-rd {suc _} _ = _
nz-intro-rd {lim _} _ = _

nz-intro : 0 < a → NonZero a
nz-intro = nz-intro-rd ∘ set

nz-elim : ⦃ NonZero a ⦄ → 0 < a
nz-elim {suc a} = z<s
nz-elim {lim f} = z<l
```

**定义 2-2-7** 非平凡序数指不等于零和一的序数. 该谓词是可判定的.

```agda
nonTrivial : Pred
nonTrivial zero       = ⊥
nonTrivial (suc zero) = ⊥
nonTrivial _          = ⊤

record NonTrivial (a : Ord) : Type where
  field .wrap : nonTrivial a
```

**事实 2-2-8** $a$ 非平凡与 $a > 1$ 等价.

```agda
nt-intro-rd : Road 1 a → NonTrivial a
nt-intro-rd {suc zero} (suc ())
nt-intro-rd {2+ a}         _ = _
nt-intro-rd {suc (lim _)}  _ = _
nt-intro-rd {lim _}        _ = _

nt-intro : 1 < a → NonTrivial a
nt-intro = nt-intro-rd ∘ set

nt-elim : ⦃ NonTrivial a ⦄ → 1 < a
nt-elim {2+ _}        = s<s z<s
nt-elim {suc (lim _)} = s<s z<l
nt-elim {lim f}       = map lim (n<fs f 1)
```

**事实 2-2-9**

- 后继序数和极限序数都是非零序数.
- 极限序数都是非平凡序数.
- 非平凡序数都是非零序数.

```agda
instance
  suc-nz : NonZero (suc a)
  suc-nz = _
  lim-nz : {w : wf f} → NonZero (lim f ⦃ w ⦄)
  lim-nz = _
  lim-nt : {w : wf f} → NonTrivial (lim f ⦃ w ⦄)
  lim-nt = _

nt-nz : ⦃ NonTrivial a ⦄ → NonZero a
nt-nz {2+ a} = _
nt-nz {suc (lim f)} = _
nt-nz {lim f} = _
```

## 加法

**互递归 2-2-10**

- (1) 定义加法 $+$.
- (2) 证明右侧加法 $λx, a + x$ 保持 $<$.

我们约定今后区分左右侧运算始终是以 $λ$ 绑定变量为基准的——$λ$ 绑定变量在二元运算符的右侧就叫右侧运算, 在左侧就叫左侧加法.

```agda
_+_ : Ord → Ord → Ord; infixl 7 _+_
+-pres-rd : (a +_) preserves Road

+-pres : (a +_) preserves _<_
+-pres = map +-pres-rd
```

**定义 2-2-10-(1)** 加法 $a + b$, 讨论 $b$.

$$
\begin{aligned}
a + 0 & = a \\
a + b'^+ & = (a + b')^+ \\
a + \lim(f) & = \lim (λ n, a + f(n))
\end{aligned}
$$

其中第三行要求说明 $λ n, a + f(n)$ 是良构的, 由定理 2-2-10-(2) 及 $f$ 良构即得. ∎

```agda
a + zero = a
a + suc b = suc (a + b)
a + lim f = lim (λ n → a + f n) ⦃ +-pres it ⦄
```

**定理 2-2-10-(2)** 右侧加法 $λx, a + x$ 保持 $<$.  
**证明** 假设 $r : x < y$, 要证 $a + x < a + y$. 对路径 $r$ 归纳.

- 若 $r = 0 : x < x^+$, 有 $a + x < (a + x)^+ = a + x^+$.
- 若 $r = r'^+ : x < y^+$, 有 $r' : x < y$, 于是 $a + x < a + y < (a + y)^+ = a + y^+$.
- 若 $r = \text{lim}(r') : x < \text{lim}(f)$, 有 $r' : x < f(n)$, 于是 $a + x < a + f(n) < \lim (λ n, a + f(n)) = a + \lim(f)$. ∎

```agda
+-pres-rd zero = zero
+-pres-rd (suc r) = suc (+-pres-rd r)
+-pres-rd (lim r) = lim ⦃ _ ⦄ (+-pres-rd r)
```

**事实 2-2-11** 零是加法的右幺元.  
**证明** 依定义. ∎

```agda
a+-id : a + 0 ≡ a
a+-id = refl
```

**定理 2-2-12** 零是加法的左幺元.  
**证明** 要证 $0 + a = a$. 对 $a$ 归纳.

- 若 $a = 0$, 有 $0 + 0 = 0$.
- 若 $a = a'^+$, 有归纳假设 $0 + a' = a'$, 于是 $0 + a'^+ = (0 + a')^+ = a'^+$.
- 若 $a = \lim(f)$, 有归纳假设 $∀n, 0 + f(n) = f(n)$, 于是 $0 + \lim(f) = \lim(λ n, 0 + f(n)) =^{\text{ext}} \lim(λ n, f(n)) = \lim(f)$. 其中 $=^{\text{ext}}$ 表示依赖函数外延性. ∎

```agda
+a-id : 0 + a ≡ a
+a-id {(zero)} = refl
+a-id {suc a} = cong suc +a-id
+a-id {lim f} = limExt λ _ → +a-id
```

**定理 2-2-13** 加法满足结合律 $a + (b + c) = (a + b) + c$.  
**证明** 对 $c$ 归纳. 与定理 2-2-12 类似. ∎

```agda
+-assoc : a + (b + c) ≡ (a + b) + c
+-assoc {c = zero} = refl
+-assoc {c = suc _} = cong suc +-assoc
+-assoc {c = lim _} = limExt λ _ → +-assoc
```

**定理 2-2-14** 左侧加法膨胀 $≤$, 即 $x ≤ x + a$.  
**证明** 对 $a$ 归纳.

- 若 $a = 0$, 有 $x ≤ x + 0$.
- 若 $a = a'^+$, 有归纳假设 $x ≤ x + a'$, 于是 $x ≤ x + a' < x + a'^+ = x + a$.
- 若 $a = \lim(f)$, 有归纳假设 $x ≤ x + f(n)$, 于是 $x ≤ x + f(n) < x + \lim(f)$. ∎

```agda
+-infl≤ : (_+ a) inflates _≤_
+-infl≤ {a = zero} = inr refl
+-infl≤ {a = suc a} {x} = begin
  x                       ≤⟨ +-infl≤ ⟩
  x + a                   <⟨ +-pres zero₁ ⟩
  x + suc a               ∎ where open SubTreeReasoning
+-infl≤ {a = lim f} {x} = begin
  x                       ≤⟨ +-infl≤ ⟩
  x + f 0                 <⟨ f<l ⟩
  x + lim f               ∎ where open SubTreeReasoning
```

**推论 2-2-15** 左侧加法在非零序数内膨胀 $<$, 即 $x < x + a$.  
**证明** 观察定理 2-2-14 的证明不难看出. ∎

```agda
+-infl : ⦃ NonZero a ⦄ → (_+ a) inflates _<_
+-infl {a = suc a} {x} = begin-strict
  x                       ≤⟨ +-infl≤ ⟩
  x + a                   <⟨ +-pres zero₁ ⟩
  x + suc a               ∎ where open SubTreeReasoning
+-infl {a = lim f} {x} = begin-strict
  x                       ≤⟨ +-infl≤ ⟩
  x + f 0                 <⟨ f<l ⟩
  x + lim f               ∎ where open SubTreeReasoning
```

## 乘法

**互递归 2-2-16**

- 定义乘法 $a \cdot b$.
- 证明右侧乘法 $λx, a \cdot x$ 保持 $<$.

其中 $a$ 非零, 因为 $a$ 为零时没有良构的乘法定义——基本列全为零.

```agda
_*_ : (a : Ord) → Ord → ⦃ NonZero a ⦄ → Ord; infixl 8 _*_
*-pres-rd : ⦃ _ : NonZero a ⦄ → (a *_) preserves Road

*-pres : ⦃ _ : NonZero a ⦄ → (a *_) preserves _<_
*-pres = map *-pres-rd
```

**定义 2-2-16-(1)** 乘法 $a \cdot b$, 讨论 $b$.

$$
\begin{aligned}
a \cdot 0 & = 0 \\
a \cdot b'^+ & = a \cdot b' + a \\
a \cdot \lim(f) & = \lim (λ n, a \cdot f(n))
\end{aligned}
$$

其中第三行要求说明 $λ n, a \cdot f(n)$ 是良构的, 由定理 2-2-16-(2) 及 $f$ 良构即得. ∎

```agda
a * zero = 0
a * suc b = a * b + a
a * lim f = lim (λ n → a * f n) ⦃ *-pres it ⦄
```

**定理 2-2-16-(2)** 右侧乘法 $λx, a \cdot x$ 保持 $<$.  
**证明** 假设 $r : x < y$, 要证 $a \cdot x < a \cdot y$. 对路径 $r$ 归纳.

- 若 $r = 0 : x < x^+$, 由于 $a$ 非零, 由推论 2-2-15 有 $a \cdot x < a \cdot x + a = a \cdot x^+$.
- 若 $r = r'^+ : x < y^+$, 有 $r' : x < y$, 于是 $a \cdot x < a \cdot y < a \cdot y + a = a \cdot y^+$.
- 若 $r = \text{lim}(r') : x < \text{lim}(f)$, 有 $r' : x < f(n)$, 于是 $a \cdot x < a \cdot f(n) < \lim (λ n, a \cdot f(n)) = a \cdot \lim(f)$. ∎

```agda
*-pres-rd zero = set +-infl
*-pres-rd {a} {x} (suc {b} r) = begin-strict
  a * x                   <⟨ *-pres-rd r ⟩
  a * b                   <⟨ set +-infl ⟩
  a * b + a               ∎ where open RoadReasoning
*-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a * x                   <⟨ *-pres-rd r ⟩
  a * f n                 <⟨ f<l-rd ⟩
  a * lim f               ∎ where open RoadReasoning
```

**事实 2-2-17** 左侧乘法尊重相等, 即 $a = b$ 蕴含 $a ⋅ c = b ⋅ c$, 其中 $a, b$ 非零.

```agda
*a-cong : {nza : NonZero a} {nzb : NonZero b} → a ≡ b → (a * c) ⦃ nza ⦄ ≡ (b * c) ⦃ nzb ⦄
*a-cong refl = refl
```

**事实 2-2-18** 零是乘法的右零元.

```agda
a*-z : ⦃ _ : NonZero a ⦄ → a * 0 ≡ 0
a*-z = refl
```

**定理 2-2-19** 一是乘法的右幺元.  
**证明** 由定义, 归结为零是加法的左幺元. ∎

```agda
a*-id : ⦃ _ : NonZero a ⦄ → a * 1 ≡ a
a*-id {a} =               begin-equality
  a * 1                   ≈⟨ refl ⟩
  0 + a                   ≈⟨ +a-id ⟩
  a                       ∎ where open SubTreeReasoning
```

**定理 2-2-20** 一是乘法的左幺元.  
**证明** 与定理 2-2-12 类似. ∎

```agda
*a-id : 1 * a ≡ a
*a-id {(zero)} = refl
*a-id {suc a} = cong suc *a-id
*a-id {lim f} = limExt λ _ → *a-id
```

**推论 2-2-21** $a ⋅ 2 = a + a$.  
**证明** 由定理 2-2-19 即得. ∎

```
*-2 : ⦃ _ : NonZero a ⦄ → a * 2 ≡ a + a
*-2 {a} =                 begin-equality
  a * 2                   ≈⟨ refl ⟩
  a * 1 + a               ≈⟨ cong (_+ a) a*-id ⟩
  a + a                   ∎ where open SubTreeReasoning
```

**定理 2-2-22** 乘法满足分配律 $a \cdot (b + c) = a \cdot b + a \cdot c$.  
**证明** 对 $c$ 归纳.

- 若 $c = 0$, 有 $a \cdot (b + 0) = a \cdot b = a \cdot b + a \cdot 0$.
- 若 $c = \lim(f)$, 有归纳假设 $∀n, a \cdot (b + f(n)) = a \cdot b + a \cdot f(n)$, 于是 $a \cdot (b + \lim(f)) = a \cdot b + a \cdot \lim(f)$.
- 若 $c = c'^+$, 有归纳假设 $a \cdot (b + c') = a \cdot b + a \cdot c'$, 于是

$$
\begin{aligned}
a \cdot (b + c'^+) & = a \cdot (b + c') + a \\
& = a \cdot b + a \cdot c' + a \\
& = a \cdot b + (a \cdot c' + a) \\
& = a \cdot b + a \cdot c'^+
\end{aligned}
$$

```agda
*-distrib : ⦃ _ : NonZero a ⦄ → a * (b + c) ≡ a * b + a * c
*-distrib {c = zero} = refl
*-distrib {c = lim _} = limExt λ _ → *-distrib
*-distrib {a} {b} {c = suc c} = begin-equality
  a * (b + suc c)         ≈⟨ refl ⟩
  a * (b + c) + a         ≈⟨ cong (_+ a) *-distrib ⟩
  a * b + a * c + a       ≈˘⟨ +-assoc ⟩
  a * b + (a * c + a)     ≈⟨ refl ⟩
  a * b + (a * suc c)     ∎ where open SubTreeReasoning
```

**事实 2-2-23** 积非零.  
**证明** 依定义. ∎

```agda
*-nz : ⦃ _ : NonZero a ⦄ ⦃ _ : NonZero b ⦄ → NonZero (a * b)
*-nz {a = suc a} {b = suc b} = _
*-nz {a = suc a} {b = lim f} = _
*-nz {a = lim f} {b = suc b} = _
*-nz {a = lim f} {b = lim f₁} = _
```

**定理 2-2-24** 乘法满足结合律 $a \cdot (b \cdot c) = (a \cdot b) \cdot c$.  
**证明** 对 $c$ 归纳. 零和极限的情况与定理 2-2-22 类似. 对于后继的情况有

$$
\begin{aligned}
a \cdot (b \cdot c'^+) & = a \cdot (b \cdot c' + b) \\
& = a \cdot (b \cdot c') + a \cdot b \\
& = (a \cdot b) \cdot c' + a \cdot b \\
& = (a \cdot b) \cdot c'^+ \quad ∎
\end{aligned}
$$

```agda
module _ {a} {b} ⦃ _ : NonZero a ⦄ ⦃ _ : NonZero b ⦄ where
  instance _ = *-nz {a} {b}
  *-assoc : a * (b * c) ≡ (a * b) * c
  *-assoc {c = zero}  = refl
  *-assoc {c = lim _} = limExt λ _ → *-assoc
  *-assoc {c = suc c} =   begin-equality
    a * (b * suc c)       ≈⟨ refl ⟩
    a * (b * c + b)       ≈⟨ *-distrib ⟩
    a * (b * c) + a * b   ≈⟨ cong (_+ a * b) *-assoc ⟩
    a * b * c + a * b     ≈⟨ refl ⟩
    a * b * suc c         ∎ where open SubTreeReasoning
```

**推论 2-2-25** 非零左侧乘法在非零序数内膨胀 $≤$, 即 $x ≤ x \cdot a$, 其中 $a,x$ 非零.  
**证明** $x = x ⋅ 1 ≤ x ⋅ a$. ∎

```agda
*-infl≤ : ⦃ NonZero a ⦄ → (_* a) inflates _≤_ within NonZero
*-infl≤ {a} {x} =        begin
  x                       ≈˘⟨ a*-id ⟩
  x * 1                   ≤⟨ map-pres≤ *-pres (<→s≤ nz-elim) ⟩
  x * a                   ∎ where open SubTreeReasoning
```

**推论 2-2-26** 非平凡左侧乘法在非零序数内膨胀 $<$, 即 $x < x \cdot a$, 其中 $a$ 非平凡, $x$ 非零.  
**证明** $x = x ⋅ 1 < x ⋅ a$. ∎

```agda
*-infl : ⦃ NonTrivial a ⦄ → (_* a) inflates _<_ within NonZero
*-infl {a} {x} =          begin-strict
  x                       ≈˘⟨ a*-id ⟩
  x * 1                   <⟨ *-pres nt-elim ⟩
  x * a                   ∎ where open SubTreeReasoning
```

## 幂运算

**互递归 2-2-27**

- (1) 定义幂运算 $a^b$.
- (2) 证明右侧幂运算 $λx, a^x$ 保持 $<$.
- (3) 证明幂非零.

其中 $a$ 非平凡, 因为 $a$ 为零或一时没有良构的幂运算定义——基本列全为零或一.

```agda
_^_ : (a : Ord) → Ord → ⦃ NonTrivial a ⦄ → Ord; infix 9 _^_
^-pres-rd : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves Road
^-nz : ⦃ _ : NonTrivial a ⦄ → NonZero (a ^ b)

^-pres : ⦃ _ : NonTrivial a ⦄ → (a ^_) preserves _<_
^-pres = map ^-pres-rd
```

**定义 2-2-27-(1)** 幂运算 $a^b$, 讨论 $b$.

$$
\begin{aligned}
a^0 & = 1 \\
a^{b'^+} & = a^{b'} \cdot a \\
a^{\lim(f)} & = \lim (λ n, a^{f(n)})
\end{aligned}
$$

其中第三行要求说明 $λ n, a^{f(n)}$ 是良构的, 由定理 2-2-27-(2) 及 $f$ 良构即得. ∎

```agda
a ^ zero = 1
a ^ suc b = (a ^ b * a) ⦃ ^-nz ⦄
a ^ lim f = lim (λ n → a ^ f n) ⦃ ^-pres it ⦄
```

**定理 2-2-27-(2)** 右侧幂运算 $λx, a^x$ 保持 $<$.  
**证明** 假设 $r : x < y$, 要证 $a^x < a^y$. 对路径 $r$ 归纳.

- 若 $r = 0 : x < x^+$, 由于 $a$ 非平凡, 由推论 2-2-26 有 $a^x < a^x \cdot a = a^{x^+}$.
- 若 $r = r'^+ : x < y^+$, 有 $r' : x < y$, 于是 $a^x < a^y < a^y \cdot a = a^{y^+}$.
- 若 $r = \text{lim}(r') : x < \text{lim}(f)$, 有 $r' : x < f(n)$, 于是 $a^x < a^{f(n)} < \lim (λ n, a^{f(n)}) = a^{\lim(f)}$. ∎

```agda
^-pres-rd zero = set *-infl where instance _ = ^-nz
^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ b                   <⟨ set *-infl ⟩
  a ^ b * a               ∎ where open RoadReasoning; instance _ = ^-nz
^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^ x                   <⟨ ^-pres-rd r ⟩
  a ^ f n                 <⟨ f<l-rd ⟩
  a ^ lim f               ∎ where open RoadReasoning
```

**定理 2-2-27-(3)** 幂非零.  
**证明** 依定义. ∎

```agda
^-nz {b = zero} = _
^-nz {b = suc b} = *-nz ⦃ _ ⦄ ⦃ nt-nz ⦄
^-nz {b = lim f} = _
```

**事实 2-2-28** 左侧幂运算尊重相等, 即 $a = b$ 蕴含 $a^c = b^c$, 其中 $a, b$ 非平凡.

```agda
^a-cong : {nta : NonTrivial a} {ntb : NonTrivial b} → a ≡ b → (a ^ c) ⦃ nta ⦄ ≡ (b ^ c) ⦃ ntb ⦄
^a-cong refl = refl
```

**事实 2-2-29** 一是幂运算的右幺元.  
**证明** 由定义, 归结为一是乘法的左幺元. ∎

```agda
a^-id : ⦃ _ : NonTrivial a ⦄ → a ^ 1 ≡ a
a^-id {a} =               begin-equality
  a ^ 1                   ≈⟨ refl ⟩
  a ^ 0 * a               ≈⟨ refl ⟩
  1 * a                   ≈⟨ *a-id ⟩
  a                       ∎ where open SubTreeReasoning
```

**定理 2-2-30** 幂运算满足分配律 $a^{b + c} = a^b \cdot a^c$.  
**证明** 对 $c$ 归纳. 零和极限的情况与定理 2-2-22 类似. 对于后继的情况有

$$
\begin{aligned}
a^{b + c'^+} & = a^{b + c'} \cdot a \\
& = a^b \cdot a^{c'} \cdot a \\
& = a^b \cdot (a^{c'} \cdot a) \\
& = a^b \cdot a^{c'^+} \quad ∎
\end{aligned}
$$

```agda
module _ {a} {b} ⦃ _ : NonTrivial a ⦄ where
  instance _ = ^-nz {a}
  ^-distrib : a ^ (b + c) ≡ a ^ b * a ^ c
  ^-distrib {c = zero} = sym +a-id
  ^-distrib {c = lim _} = limExt λ _ → ^-distrib
  ^-distrib {c = suc c} =       begin-equality
    a ^ (b + suc c)             ≈⟨ refl ⟩
    a ^ (b + c) * a             ≈⟨ *a-cong ^-distrib ⟩
    (a ^ b * a ^ c * a) ⦃ _ ⦄   ≈˘⟨ *-assoc ⟩
    a ^ b * (a ^ c * a)         ≈⟨ refl ⟩
    a ^ b * (a ^ suc c)         ∎ where open SubTreeReasoning
```

**定理 2-2-31** 幂非平凡, 即 $a^b$ 非平凡, 其中 $a$ 非平凡, $b$ 非零.  
**证明** 难点在于 $a, b$ 都是后继的情况, 我们证 ${(a'^+)}^{b'^+} > 1$, 其中 $a'$ 非零.

$$
\begin{aligned}
1 & = {(a'^+)}^0 \\
& ≤ {(a'^+)}^{b'} \\
& = {(a'^+)}^{b'} \cdot 1 \\
& ≤ {(a'^+)}^{b'} \cdot a' \\
& < {(a'^+)}^{b'} \cdot a' + {(a'^+)}^{b'} \\
& = {(a'^+)}^{b'} \cdot a'^+ \\
& = {(a'^+)}^{b'^+} \quad ∎
\end{aligned}
$$

```agda
^-nt : ⦃ nta : NonTrivial a ⦄ ⦃ nzb : NonZero b ⦄ → NonTrivial (a ^ b)
^-nt {lim f} {suc b} = _
^-nt {suc a} {lim f} = _
^-nt {lim f} {lim g} = _
^-nt {suc a} {suc b} ⦃ nzb ⦄ =  nt-intro $ begin-strict
  1                             ≈⟨ refl ⟩
  suc a ^ 0                     ≤⟨ map-pres≤ ^-pres $ <s→≤ (nz-elim ⦃ _ ⦄) ⟩
  suc a ^ b                     ≈˘⟨ a*-id ⟩
  suc a ^ b * 1                 ≤⟨ map-pres≤ *-pres $ <s→≤ nt-elim ⟩
  suc a ^ b * a                 <⟨ +-infl ⟩
  suc a ^ b * a + suc a ^ b     ∎ where open SubTreeReasoning; instance _ = ^-nz
```

**定理 2-2-32** 幂运算满足结合律 ${(a^b)}^c = a^{(b⋅c)}$.  
**证明** 对 $c$ 归纳. 零和极限的情况与定理 2-2-22 类似. 对于后继的情况有

$$
\begin{aligned}
{(a^b)}^{c'^+} & = {(a^b)}^{c'} \cdot a^b \\
& = a^{b \cdot c'} \cdot a^b \\
& = a^{b \cdot c' + b} \\
& = a^{b \cdot c'^+} \quad ∎
\end{aligned}
$$

```agda
module _ {a} {b} ⦃ _ : NonTrivial a ⦄ ⦃ _ : NonZero b ⦄ where
  instance _ = ^-nt {a} {b}
  ^-assoc : (a ^ b) ^ c ≡ a ^ (b * c)
  ^-assoc {c = zero} = refl
  ^-assoc {c = lim f} = limExt λ _ → ^-assoc
  ^-assoc {c = suc c} =         begin-equality
    (a ^ b) ^ suc c             ≈⟨ refl ⟩
    ((a ^ b) ^ c * a ^ b) ⦃ _ ⦄ ≈⟨ *a-cong ^-assoc ⟩
    (a ^ (b * c) * a ^ b) ⦃ _ ⦄ ≈˘⟨ ^-distrib ⟩
    a ^ (b * c + b)             ≈⟨ refl ⟩
    a ^ (b * suc c)             ∎ where open SubTreeReasoning
```

**推论 2-2-33** 非零左侧幂运算在非平凡序数内膨胀 $≤$, 即 $x ≤ x^a$, 其中 $a$ 非零, x$ 非平凡.  
**证明** $x = x^1 ≤ x^a$. ∎

```agda
^-infl≤ : ⦃ NonZero a ⦄ → (_^ a) inflates _≤_ within NonTrivial
^-infl≤ {a} {x} =               begin
  x                             ≈˘⟨ a^-id ⟩
  x ^ 1                         ≤⟨ map-pres≤ ^-pres (<→s≤ nz-elim) ⟩
  x ^ a                         ∎ where open SubTreeReasoning
```

**推论 2-2-34** 非平凡左侧幂运算在非平凡序数内膨胀 $<$, 即 $x < x^a$, 其中 $a, x$ 非平凡.  
**证明** $x = x^1 < x^a$. ∎

```agda
^-infl : ⦃ NonTrivial a ⦄ → (_^ a) inflates _<_ within NonTrivial
^-infl {a} {x} =                begin-strict
  x                             ≈˘⟨ a^-id ⟩
  x ^ 1                         <⟨ ^-pres nt-elim ⟩
  x ^ a                         ∎ where open SubTreeReasoning
```

## 伪迭代幂次

**互递归 2-2-35**

- (1) 定义伪迭代幂次 $a ↑↑ b$
- (2) 证明右侧伪迭代幂次 $λx, a↑↑x$ 保持 $<$.
- (3) 证明伪迭代幂次非平凡.

其中 $a$ 非平凡, 因为 $a$ 为零或一时没有良构的伪迭代幂次定义——基本列全为零或一.

```agda
_^^_ : (a b : Ord) → ⦃ NonTrivial a ⦄ → Ord
^^-pres-rd : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves Road
^^-nt : ⦃ _ : NonTrivial a ⦄ → NonTrivial (a ^^ b)

^^-pres : ⦃ _ : NonTrivial a ⦄ → (a ^^_) preserves _<_
^^-pres = map ^^-pres-rd
```

**定义 2-2-35-(1)** 伪迭代幂次 $a ↑↑ b$, 讨论 $b$.

$$
\begin{aligned}
a ↑↑ 0 & = a \\
a ↑↑ b'^+ & = (a ↑↑ b) ^ a \\
a ↑↑ \lim(f) & = \lim (λ n, a ↑↑ f(n))
\end{aligned}
$$

其中第三行要求说明 $λ n, a ↑↑ f(n)$ 是良构的, 由定理 2-2-35-(2) 及 $f$ 良构即得. ∎

```agda
a ^^ zero = a
a ^^ suc b = ((a ^^ b) ^ a) ⦃ ^^-nt ⦄
a ^^ lim f = lim (λ n → a ^^ f n) ⦃ ^^-pres it ⦄
```

**定理 2-2-35-(2)** 右侧伪迭代幂次 $λx, a↑↑x$ 保持 $<$.  
**证明** 假设 $r : x < y$, 要证 $a↑↑x < a↑↑y$. 对路径 $r$ 归纳.

- 若 $r = 0 : x < x^+$, 由于 $a$ 和 $a↑↑x$ 非平凡, 由推论 2-2-34 有 $a↑↑x < (a↑↑x)^a = a↑↑x^+$.
- 若 $r = r'^+ : x < y^+$, 有 $r' : x < y$, 于是 $a↑↑x < a↑↑y < (a↑↑y) ^ a = a↑↑y^+$.
- 若 $r = \text{lim}(r') : x < \text{lim}(f)$, 有 $r' : x < f(n)$, 于是 $a↑↑x < a↑↑f(n) < \lim (λ n, a↑↑f(n)) = a↑↑\lim(f)$. ∎

```agda
^^-pres-rd {a} {x} zero = set ^-infl where instance _ = ^^-nt {a} {x}
^^-pres-rd {a} {x} (suc {b} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ b                        <⟨ set ^-infl ⟩
  (a ^^ b ^ a) ⦃ _ ⦄            ≈⟨ refl ⟩
  a ^^ suc b                    ∎ where open RoadReasoning; instance _ = ^^-nt {a} {b}
^^-pres-rd {a} {x} (lim {f} {n} r) = begin-strict
  a ^^ x                        <⟨ ^^-pres-rd r ⟩
  a ^^ f n                      <⟨ f<l-rd ⟩
  a ^^ lim f                    ∎ where open RoadReasoning
```

**定理 2-2-35-(3)** 伪迭代幂次非平凡.  
**证明** 依定义. ∎

```agda
^^-nt {b = zero} = it
^^-nt {b = suc b} = ^-nt ⦃ _ ⦄ ⦃ nt-nz ⦄
^^-nt {b = lim f} = _
```

**定理 2-2-36** 伪迭代幂次之伪: $a ↑↑ b = a ^ {(a ^ b)}$, 而不是我们期待的 $b$ 层塔 $a^{a^{a^{⋰}}}$.  
**证明** 对 $b$ 归纳. 零和极限的情况与定理 2-2-30 类似. 对于后继的情况有

$$
\begin{aligned}
a ↑↑ b'^+ & = (a ↑↑ b') ^ a \\
& = {(a^{(a^{b'})})}^a \\
& = a^{(a^{b'} \cdot a)} \\
& = a^{(a^{b'^+})} \quad ∎
\end{aligned}
$$

```agda
^^-fake : ⦃ _ : NonTrivial a ⦄ → a ^^ b ≡ a ^ (a ^ b)
^^-fake {a} {b = zero}  = sym *a-id
^^-fake {a} {b = lim f} = limExt λ _ → ^^-fake
^^-fake {a} {b = suc b} =       begin-equality
  a ^^ suc b                    ≈⟨ refl ⟩
  ((a ^^ b) ^ a) ⦃ _ ⦄          ≈⟨ ^a-cong ^^-fake ⟩
  ((a ^ (a ^ b)) ^ a) ⦃ _ ⦄     ≈⟨ ^-assoc ⟩
  a ^ (a ^ b * a) ⦃ _ ⦄         ≈⟨ refl ⟩
  a ^ (a ^ suc b)               ∎ where open SubTreeReasoning; instance _ = ^-nz
```

为了定义真正的迭代幂次, 我们需要研究不动点, 这将在后篇展开.
