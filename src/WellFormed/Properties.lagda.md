---
title: 形式化大数数学 (2.1 - 良构树序数的性质)
zhihu-tags: Agda, 大数数学, 序数
zhihu-url: https://zhuanlan.zhihu.com/p/715404245
---

# 形式化大数数学 (2.1 - 良构树序数的性质)

> 交流Q群: 893531731  
> 本文源码: [Properties.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Properties.lagda.md)  
> 高亮渲染: [Properties.html](https://choukh.github.io/agda-googology/WellFormed.Properties.html)  

```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Properties where
open import WellFormed.Base
```

[上一篇](https://zhuanlan.zhihu.com/p/711649863)我们定义了良构树序数并证明了一些基本性质, 本文将继续讨论它的更多性质.

## 序数函数

我们先定义关于序数函数的一些性质.

**定义 2-1-0** 我们把

- 序数函数的类型记作 $\text{Func}$, 并约定用大写的 $F$ 表示序数函数.
- 序数的一元关系类型记作 $\text{Pred}$, 也叫做序数上的谓词 (predicate).
- 序数的二元关系类型记作 $\text{Rel}$

```agda
Func : Type
Func = Ord → Ord
private variable F : Func

Pred : Type₁
Pred = Ord → Type

Rel : Type₁
Rel = Ord → Ord → Type
```

**定义 2-1-1** 我们说一个序数函数 $F$ **保持**一个序数关系 $\sim$, 当且仅当对任意序数 $x, y$ 都有 $x \sim y \to F(x) \sim F(y)$.

```agda
_preserves_ : Func → Rel → Type
F preserves _~_ = ∀ {x y} → x ~ y → F x ~ F y
```

**事实 2-1-2** 如果 $F$ 保持 $\lt$, 那么 $F$ 保持 $\leq$.

```agda
map-pres≤ : F preserves _<_ → F preserves _≤_
map-pres≤ pres (inl p)    = <→≤ (pres p)
map-pres≤ pres (inr refl) = inr refl
```

**定义 2-1-3** 我们说一个序数函数 $F$ **单射**一个序数关系 $\sim$, 当且仅当对任意序数 $x, y$ 都有 $F(x) \sim F(y) \to x \sim y$.

```agda
_injects_ : Func → Rel → Type
F injects _~_ = ∀ {x y} → F x ~ F y → x ~ y
```

**事实 2-1-4** 如果 $F$ 单射 $=$ 且单射 $\lt$, 那么 $F$ 单射 $\leq$.

```agda
map-inj≤ : F injects _≡_ → F injects _<_ → F injects _≤_
map-inj≤ inj inj< (inl p) = inl (inj< p)
map-inj≤ inj inj< (inr p) = inr (inj p)
```

## 一些约定

**记法 2-1-5** 隐参版极限构造子: 它们与原版的区别在于良构条件为隐式参数, 从而允许从上下文自动推断出它们, 而不用一一显式写出.

```agda
lim- : (f : Seq) {w : wf f} → Ord
lim- f {w} = lim f ⦃ w ⦄
```

如果我们有 $a$ 通往 $\lim f$ 的序列第 $n$ 项的路径 $r$, 那么我们把 $a$ 通往 $\lim f$ 的路径记作 $\text{rd}[n](r)$.

```agda
rd[_] : (n : ℕ) {w : wf f} → Road a (f n) → Road a (lim f ⦃ w ⦄)
rd[_] n = lim {n = n} ⦃ _ ⦄
```

如果我们有 $a$ 小于 $\lim f$ 的序列第 $n$ 项的证明 $r$, 那么我们把 $a$ 小于 $\lim f$ 的证明记作 $\text{<}[n](r)$.

```agda
<[_] : (n : ℕ) {w : wf f} → a < f n → a < lim f ⦃ w ⦄
<[_] n = map rd[ n ]
```

**约定 2-1-6** 鉴于路径关系与子树关系的高度可互换性, 我们今后在自然语言中会适当地混淆两者, 例如把路径的构造说成是子树关系的证明, 或反之. 读者应该理解为是调用了上一篇的引理进行了两者的转换.

树序数的归纳定义允许我们快速判定一个序数是否是极限序数.

**定义 2-1-7** 极限序数谓词: 它仅在遇到极限序数时为真. 该谓词是可判定的.

```agda
isLim : Pred
isLim zero = ⊥
isLim (suc a) = ⊥
isLim (lim f) = ⊤
```

**记法 2-1-8** 极限序数的基本列: 如果 $a$ 是极限序数, 那么我们用 $a[n]$ 表示其基本列的第 $n$ 项. 由序数的定义有 $a[n] < a[n^+]$.

```agda
_[_] : (a : Ord) → ⦃ isLim a ⦄ → Seq
_[_] (lim f) = f

[]-wf : ⦃ _ : isLim a ⦄ → a [ n ] < a [ suc n ]
[]-wf {lim f} = it
```

**定义 2-1-9** 自然数到序数的嵌入 $\text{fin} : ℕ → \text{Ord}$

$$
\text{fin}(n) := \text{suc}^n(0)
$$

其中后继函数的上标 $n$ 表示迭代 $n$ 次.

```agda
open import Lower public using (_∘ⁿ_)
fin : Seq
fin n = (suc ∘ⁿ n) zero
```

非形式地, 后文中我们把 $\text{fin}$ 视作类型强转 (coercion).

**约定 2-1-10** 数字字面量既可以表示自然数, 也可以表示序数. Agda 使用[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能实现该约定.

```agda
open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }
```

## 一些引理

**事实 2-1-11** 构造子的单射性

- $a^+ =b ^+ → a = b$
- $\lim f = \lim g → f = g$

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : {wff : wf f} {wfg : wf g} → Ord.lim f ⦃ wff ⦄ ≡ lim g ⦃ wfg ⦄ → f ≡ g
lim-inj refl = refl
```

**事实 2-1-12** 极限路径的反演: 如果 $b$ 小于极限序数 $a$, 那么存在一个自然数 $n$ 使得 $b$ 小于 $a[n]$.

```agda
lim-inv-rd : ⦃ _ : isLim a ⦄ → Road b a → Σ[ n ∈ ℕ ] Road b (a [ n ])
lim-inv-rd (lim r) = _ , r

lim-inv : ⦃ _ : isLim a ⦄ → b < a → Σ[ n ∈ ℕ ] b < a [ n ]
lim-inv r with lim-inv-rd (set r)
... | n , r = n , ∣ r ∣₁
```

鉴于互递归证明的特性, 我们有时会先声明定理, 然后再证明其所需的引理, 最后再证明定理本身.

**定理 2-1-13** 互递归地, 有

$$
\begin{aligned}
(1)& \quad a < b → 0 < b \\
(2)& \quad 0 < a^+
\end{aligned}
$$

```agda
z<b-rd : Road a b → Road 0 b
z<s-rd : Road 0 (suc a)

z<b : a < b → 0 < b
z<b = map z<b-rd

z<s : 0 < suc a
z<s = ∣ z<s-rd ∣₁
```

**引理 2-1-14** 基本列的后继项必然大于零.  
**证明** 给定基本列 $f$, 由于 $f(n)<f(n^+)$, 由定理 2-1-13-(1) 即证. ∎

```agda
z<fs : ∀ f n → ⦃ _ : wf f ⦄ → 0 < f (suc n)
z<fs f n = z<b it
```

**引理 2-1-15** 极限序数必然大于零.  
**证明** 由 $\text{<}[1]$, 我们证明其基本列第 $1$ 项大于零, 而这由引理 2-1-14 即证. ∎

```agda
z<l : {w : wf f} → 0 < lim f ⦃ w ⦄
z<l {f} {w} = <[ 1 ] (z<fs f 0 ⦃ w ⦄)
```

**定理 2-1-13-(1)** $a < b → 0 < b$.  
**证明** 对路径 $r : a < b$ 归纳.

- 若 $r = 0 : a < a^+$, 由定理 2-1-13-(2) 即得 $0 < a^+$.
- 若 $r = r'^+ : a < b^+$, 由定理 2-1-13-(2) 即得 $0 < b^+$.
- 若 $r = \lim(r') : a < \lim(f)$, 由引理 2-1-15 即得 $0 < \lim(f)$. ∎

```agda
z<b-rd zero = z<s-rd
z<b-rd (suc r) = z<s-rd
z<b-rd (lim r) = set z<l
```

**定理 2-1-13-(2)** $0 < a^+$.  
**证明** 对 $a$ 归纳.

- 若 $a = 0$, 有 $0 : 0 < 0^+$.
- 若 $a = a'^+$, 有归纳假设 $r : 0 < a'^+$, 所以 $r^+ : 0 < a'^{++}$.
- 若 $a = \lim(f)$, 要证 $a < \lim(f)^+$, 由路径构造子 $\text{suc}$ 及引理 2-1-15 即得. ∎

```agda
z<s-rd {(zero)} = zero
z<s-rd {suc a} = suc z<s-rd
z<s-rd {lim f} = suc (set z<l)
```

**推论 2-1-16** 零小于等于任何序数.  
**证明** 对 $a$ 归纳. 零的情况由自反性, 后继的情况由2-1-13-(2), 极限的情况由引理 2-1-15 即得. ∎

```agda
z≤ : 0 ≤ a
z≤ {(zero)} = inr refl
z≤ {suc _}  = inl z<s
z≤ {lim _}  = inl z<l
```

**定理 2-1-17** 互递归地, 有

- (1) $a < b \to a^+ ≤ b$.
- (2) 后继运算保持 $<$.

```agda
<→s≤-rd : Road a b → NSRoad (suc a) b
s<s-rd : suc preserves Road

<→s≤ : a < b → suc a ≤ b
<→s≤ = rec isProp≤ (ns→≤ ∘ <→s≤-rd)

s<s : suc preserves _<_
s<s = map s<s-rd
```

**定理 2-1-17-(1)** $a < b \to a^+ ≤ b$.  
**证明** 对路径 $r : a < b$ 归纳.

- 若 $r = 0 : a < a^+$, 由自反性即得 $a^+ ≤ a^+$.
- 若 $r = r'^+ : a < b^+$, 则有 $r' : a < b$. 由定理 2-1-17-(2) 即得 $a^+ ≤ b^+$.
- 若 $r = \lim(r') : a < \lim(f)$, 则有 $r' : a < f(n)$. 由定理 2-1-17-(2) 有 $a^+ < f(n)^+$, 由归纳假设有 $f(n)^+ ≤ f(n^+)$, 由传递性即得 $a^+ < \lim(f)$. ∎

```agda
<→s≤-rd zero = inr refl
<→s≤-rd (suc r) = inl (s<s-rd r)
<→s≤-rd {a} (lim {f} {n} r) = inl $ begin-strict
  suc a           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd (set it) ⟩
  f (suc n)       <⟨ f<l-rd ⟩
  lim f           ∎ where open RoadReasoning
```

**定理 2-1-17-(2)** 后继运算保持 $<$.  
**证明** 对路径 $r : a < b$ 归纳, 要证 $a^+ < b^+$.

- 若 $r = 0 : a < a^+$, 有 $0 : a^+ < a^{++}$.
- 若 $r = r'^+ : a < b^+$, 则有 $r' : a < b$. 由归纳假设即得 $a^+ < b^+$.
- 若 $r = \lim(r') : a < \lim(f)$, 则有 $r' : a < f(n)$. 与定理 2-1-17-(1) 同理可证 $a^+ < \lim(f)$, 再由路径构造子 $\text{suc}$ 即得 $a^+ < \lim(f)^+$. ∎

```agda
s<s-rd zero = zero
s<s-rd (suc r) = suc (s<s-rd r)
s<s-rd {x} (lim {f} {n} r) = suc $ begin-strict
  suc x           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd (set it) ⟩
  f (suc n)       <⟨ f<l-rd ⟩
  lim f           ∎ where open RoadReasoning
```

**定理 2-1-18** 后继运算单射 $<$.  
**证明** 对路径 $r : a^+ < b^+$ 归纳, 要证 $a < b$.

- 若 $r = 0 : a^+ < a^{++}$, 有 $0 : a < a^+$.
- 若 $r = r'^+ : a^+ < b^+$, 则有 $r' : a^+ < b$. 由传递性即得 $a < a^+ < b$.
- 没有 $r = \lim(r') : a^+ < \lim(f)$ 的情况, 因为 $\lim(f)$ 不可能是后继序数. ∎

```agda
s<s-inj-rd : suc injects Road
s<s-inj-rd zero = zero
s<s-inj-rd (suc r) = rd-trans zero r

s<s-inj : suc injects _<_
s<s-inj = map s<s-inj-rd
```

**推论 2-1-19** 后继运算保持 $\leq$, 且单射 $\leq$.  
**证明** 由事实 2-1-2 和定理 2-1-17-(2) 可证保持; 由事实 2-1-4, 事实 2-1-11 和定理 2-1-18 可证单射. ∎

```agda
s≤s : suc preserves _≤_
s≤s = map-pres≤ s<s

s≤s-inj : suc injects _≤_
s≤s-inj = map-inj≤ suc-inj s<s-inj
```

**定理 2-1-20** 定理 2-1-17-(1) 的逆命题 $a^+ ≤ b → a < b$ 成立.  
**证明** 对 $b$ 归纳, 且讨论 $r : a^+ ≤ b$.

- $b = 0$ 的情况不可能.
- 若 $b = b'^+$ 且 $a^+ < b'^+$, 由推论 2-1-19 有 $a < b'$, 所以 $a < b'^+$.
- 若 $b = b'^+$ 且 $a^+ = b'^+$, 目标改写变为 $b' < b$, 显然成立.
- 若 $b = \lim(f)$, $r$ 只能为 $r = \lim(r') : a^+ < \lim(f)$ 且 $r' : a^+ < f(n)$, 由传递性即得 $a < a^+ < f(n) < \lim(f)$. ∎

```agda
s≤→<-rd : NSRoad (suc a) b → Road a b
s≤→<-rd {b = suc b} (inl r)       = suc (s<s-inj-rd r)
s≤→<-rd {b = suc b} (inr refl)    = zero
s≤→<-rd {b = lim f} (inl (lim r)) = lim (rd-trans zero r)

s≤→< : suc a ≤ b → a < b
s≤→< (inl r)    = map (s≤→<-rd ∘ inl) r
s≤→< (inr refl) = zero₁
```

**定理 2-1-21** 后继运算在极限序数下封闭.  
**证明** 要证对任意 $b$ 小于极限序数 $a$ 都有 $b^+ < a$. 讨论 $r : b < a$, 只能有 $r = \lim(r') : b < a$, 且 $r' : b < a[n]$. 由定理 2-1-17 即传递性即得 $b^+ < a[n]^+ ≤ a$. ∎

```agda
s<l-rd : ⦃ _ : isLim a ⦄ → Road b a → Road (suc b) a
s<l-rd {a} {b} (lim {n} r) = begin-strict
  suc b           <⟨ s<s-rd r ⟩
  suc (a [ n ])   ≤⟨ <→s≤-rd f<l-rd ⟩
  a               ∎ where open RoadReasoning

s<l : ⦃ _ : isLim a ⦄ → b < a → suc b < a
s<l = map s<l-rd
```

**定理 2-1-22** 直接前驱在极限序数上封闭.  
**证明** 要证对任意极限序数 $a ≤ b^+$ 有 $a ≤ b$. 讨论 $a ≤ b^+$.

- 不可能有 $a = b^+$ 的情况, 因为 $b^+$ 不可能是极限序数.
- 若 $a < a^+$, 有 $a = a$.
- 若 $a < b^+$, 必然有 $a < b$. ∎

```agda
l≤p-rd : ⦃ _ : isLim a ⦄ → NSRoad a (suc b) → NSRoad a b
l≤p-rd {lim f} (inl zero)    = inr refl
l≤p-rd {lim f} (inl (suc r)) = inl r

l≤p : ⦃ _ : isLim a ⦄ → a ≤ suc b → a ≤ b
l≤p {lim f} (inl r) = ns→≤ (l≤p-rd (inl (set r)))
```

## ω的性质

**定义 2-1-23** 由定义 2-1-9, 显然 $\text{fin}$ 是良构序列, 我们把 $\lim(\text{fin})$ 记作 $\omega$.

```agda
instance
  fin-wf : wf fin
  fin-wf = zero₁

ω : Ord
ω = lim fin
```

**引理 2-1-24** 有限序数 $n$ 都小于 $\omega$.  
**证明** 对 $n$ 归纳.

- 若 $n$ 为零, 由引理 2-1-15 可知零小于极限序数.
- 若 $n$ 为后继, 由定理 2-1-21 可知后继序数小于极限序数, 只要其直接前驱小于该极限序数, 而这是归纳假设. ∎

```agda
n<ω : fin n < ω
n<ω {n = zero}  = z<l
n<ω {n = suc n} = s<l n<ω
```

**引理 2-1-25** 任意基本列的第 $n$ 项大于等于 $n$.  
**证明** 对 $n$ 归纳.

- 若 $n$ 为零, 显然 $0 ≤ f(0)$.
- 若 $n$ 为后继, 由归纳假设 $n ≤ f(n)$ 可得 $n^+ ≤ f(n)^+ < f(n^+)$. ∎

```agda
n≤fn : ∀ f → ⦃ _ : wf f ⦄ → fin n ≤ f n
n≤fn {n = zero} f   = z≤
n≤fn {n = suc n} f  = begin
  fin (suc n)         ≤⟨ s≤s (n≤fn f) ⟩
  suc (f n)           ≤⟨ <→s≤ it ⟩
  f (suc n)           ∎ where open SubTreeReasoning
```

**推论 2-1-26** 任意基本列的第 $n^+$ 项大于 $n$.  
**证明** $n ≤ f(n) < f(n^+)$. ∎

```agda
n<fs : ∀ f n → ⦃ _ : wf f ⦄ → fin n < f (suc n)
n<fs f _ = ≤-<-trans (n≤fn f) it
```

**引理 2-1-27** 没有极限序数小于 $\omega$.  
**证明** 假设有这样的序数 $a$. 由事实 2-1-12, 存在 $n$ 使得 $a < n$. 但由引理 2-1-25 又有 $n ≤ a[n] < a$. 由传递性有 $n < n$, 违反 $<$ 的反自反性. ∎

```agda
l≮ω : ⦃ isLim a ⦄ → a ≮ ω
l≮ω a@{lim f} r = let n , r = lim-inv r in <-irrefl refl $ begin-strict
  fin n               ≤⟨ n≤fn f ⟩
  a [ n ]             <⟨ f<l ⟩
  a                   <⟨ r ⟩
  fin n               ∎ where open SubTreeReasoning
```

**引理 2-1-28** 忽略非同株, $\omega$ 是最小的极限序数.  
**证明** 对任意与 $\omega$ 同株的极限序数 $a$, 由推论 2-0-34, 讨论 $\omega$ 与 $a$ 的大小关系. 若 $a < \omega$, 由引理 2-1-27 可得矛盾. 所以只能有 $ω ≤ a$. ∎

```agda
ω≤l : ⦃ isLim a ⦄ → ω < b → a < b → ω ≤ a
ω≤l {lim f} r s with <-connex r s
... | inl r           = inl r
... | inr (inr refl)  = inr refl
... | inr (inl r)     = ⊥-elim $ l≮ω r
```

**引理 2-1-29** $\text{fin}$ 单射 $=$.  
**证明** 对 $m, n$ 归纳即得. ∎

```agda
fin-inj : fin m ≡ fin n → m ≡ n
fin-inj {(zero)} {(zero)} eq = refl
fin-inj {suc m}  {suc n}  eq = cong suc $ fin-inj $ suc-inj eq
```

**引理 2-1-30** $\text{fin}$ 满射 $\omega$.  
**证明** 要证对任意 $a < ω$ 都存在 $n$ 使得 $n = a$. 对 $a$ 归纳.

- 若 $a = 0$, 取 $n = 0$ 即可.
- 若 $a = a'^+$, 由归纳假设可得一个 $n' = a'$. 取 $n = n'^+$ 即可.
- 若 $a = \lim(f)$, 由引理 2-1-27 可得矛盾. ∎

```agda
fin-suj : a < ω → Σ[ n ∈ ℕ ] fin n ≡ a
fin-suj {(zero)} r  = 0 , refl
fin-suj {suc _}  r  with fin-suj (<-trans zero₁ r)
... | n , refl      = suc n , refl
fin-suj {lim f}  r  = ⊥-elim $ <-irrefl refl $ begin-strict
  ω                   ≤⟨ ω≤l zero₁ (<-trans r zero₁) ⟩
  lim f               <⟨ r ⟩
  ω                   ∎ where open SubTreeReasoning
```

**定理 2-1-31** $ℕ$ 与小于 $\omega$ 的序数同构.  
**证明** $\text{fin}$ 提供了正映射, 引理 2-1-30 提供了逆映射. 结合引理 2-1-29 可以说明它们互逆. ∎

```agda
ℕ≡ω : ℕ ≡ Σ Ord (_< ω)
ℕ≡ω = pathToEq $ isoToPath $ iso
  (λ n → fin n , n<ω)
  (λ (a , a<ω) → fst (fin-suj a<ω))
  (λ a → ΣPathP $ eqToPath (snd $ fin-suj _) , toPathP (squash₁ _ _))
  (λ n → eqToPath $ fin-inj $ snd $ fin-suj _)
  where open import Cubical.Foundations.Isomorphism
```
