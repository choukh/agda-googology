---
title: 形式化大数数学 (2.1 - 良构树序数的性质)
zhihu-tags: Agda, 大数数学, 序数
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

**定义 2-1-0** 我们把序数函数的类型简记作 $\text{Func}$, 序数的二元关系的类型简记作 $\text{Rel}$, 并约定用大写的 $F$ 表示序数函数.

```agda
Func : Type
Func = Ord → Ord

Rel : Type₁
Rel = Ord → Ord → Type

private variable F : Func
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

**事实 2-1-4** 如果 $F$ 单射 $\lt$, 那么 $F$ 单射 $\leq$.

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

**事实 2-1-7** 极限序数的判定: 树序数的归纳定义允许我们快速判断一个序数是否是极限序数.

```agda
IsLim : Ord → Type
IsLim zero = ⊥
IsLim (suc a) = ⊥
IsLim (lim f) = ⊤
```

**记法 2-1-8** 极限序数的基本列: 如果 $a$ 是极限序数, 那么我们用 $a[n]$ 表示其基本列的第 $n$ 项. 由序数的定义有 $a[n] < a[n^+]$.

```agda
_[_] : (a : Ord) → ⦃ IsLim a ⦄ → Seq
_[_] (lim f) = f

[]-wf : ⦃ _ : IsLim a ⦄ → a [ n ] < a [ suc n ]
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
lim-inv-rd : ⦃ _ : IsLim a ⦄ → Road b a → Σ[ n ∈ ℕ ] Road b (a [ n ])
lim-inv-rd (lim r) = _ , r

lim-inv : ⦃ _ : IsLim a ⦄ → b < a → Σ[ n ∈ ℕ ] b < a [ n ]
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
**证明** 给定基本列 $f$, 由于 $f(n)<f(n^+)$, 由定理 2-1-12 即证. ∎

```agda
z<fs : ∀ f n → ⦃ _ : wf f ⦄ → 0 < f (suc n)
z<fs f n = z<b it
```

**引理 2-1-15** 极限序数必然大于零.  
**证明** 由 $\text{<}[n]$, 我们证明其基本列第 $1$ 项大于零, 而这由引理 2-1-14 即证. ∎

```agda
z<l : {w : wf f} → 0 < lim f ⦃ w ⦄
z<l {f} {w} = <[ 1 ] (z<fs f 0 ⦃ w ⦄)
```

**定理 2-1-13-(1)** $a < b → 0 < b$.  
**证明** 对路径 $r : a < b$ 归纳.

- 若 $r : a < a^+$, 由定理 2-1-13-(2) 即得 $0 < a^+$.
- 若 $r : a < b^+$, 由定理 2-1-13-(2) 即得 $0 < b^+$.
- 若 $r : a < \lim(f)$, 由引理 2-1-15 即得 $0 < \lim(f)$. ∎

```agda
z<b-rd zero = z<s-rd
z<b-rd (suc r) = z<s-rd
z<b-rd (lim r) = set z<l
```

**定理 2-1-13-(2)** $0 < a^+$.  
**证明** 对 $a$ 归纳.

```agda
z<s-rd {(zero)} = zero
z<s-rd {suc a} = suc z<s-rd
z<s-rd {lim f} = suc (lim (set (z<fs f 1)))
```

**推论 2-1-16**

```agda
z≤ : 0 ≤ a
z≤ {(zero)} = inr refl
z≤ {suc _}  = inl z<s
z≤ {lim _}  = inl z<l
```

**定理 2-1-17** 后继运算的保序性

```agda
<→s≤-rd : Road a b → NSRoad (suc a) b
s<s-rd : suc preserves Road

<→s≤ : a < b → suc a ≤ b
<→s≤ = rec isProp≤ (ns→≤ ∘ <→s≤-rd)

s<s : suc preserves _<_
s<s = map s<s-rd
```

**定理 2-1-17-(1)**

```agda
<→s≤-rd zero = inr refl
<→s≤-rd (suc r) = inl (s<s-rd r)
<→s≤-rd {a} (lim {f} {n} r) = inl $ lim $ begin-strict
  suc a           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd (set it) ⟩
  f (suc n)       ∎ where open RoadReasoning
```

**定理 2-1-17-(2)**

```agda
s<s-rd zero = zero
s<s-rd (suc r) = suc (s<s-rd r)
s<s-rd {x} (lim {f} {n} r) = suc $ begin-strict
  suc x           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd f<l-rd ⟩
  lim f           ∎ where open RoadReasoning
```

**推论 2-1-18**

```agda
s<s-inj-rd : suc injects Road
s<s-inj-rd zero = zero
s<s-inj-rd (suc r) = rd-trans zero r

s<s-inj : suc injects _<_
s<s-inj = map s<s-inj-rd
```

**定理 2-1-19**

```agda
s≤→<-rd : NSRoad (suc a) b → Road a b
s≤→<-rd {b = suc b} (inl r)       = suc (s<s-inj-rd r)
s≤→<-rd {b = suc b} (inr refl)    = zero
s≤→<-rd {b = lim f} (inl (lim r)) = lim (rd-trans zero r)

s≤→< : suc a ≤ b → a < b
s≤→< (inl r)    = map (s≤→<-rd ∘ inl) r
s≤→< (inr refl) = zero₁
```

**推论 2-1-20**

```agda
s≤s : suc preserves _≤_
s≤s = map-pres≤ s<s

s≤s-inj : suc injects _≤_
s≤s-inj = map-inj≤ suc-inj s<s-inj
```

**定理 2-1-21**

```agda
s<l-rd : {w : wf f} → Road a (lim f ⦃ w ⦄) → Road (suc a) (lim f ⦃ w ⦄)
s<l-rd {a} (lim {f} {n} r) = begin-strict
  suc a           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd f<l-rd ⟩
  lim- f          ∎ where open RoadReasoning

s<l : {w : wf f} → a < lim f ⦃ w ⦄ → suc a < lim f ⦃ w ⦄
s<l = map s<l-rd
```

**定理 2-1-22**

```agda
l≤p-rd : {w : wf f} → NSRoad (lim f ⦃ w ⦄) (suc a) → NSRoad (lim f ⦃ w ⦄) a
l≤p-rd (inl zero)    = inr refl
l≤p-rd (inl (suc r)) = inl r

l≤p : {w : wf f} → lim f ⦃ w ⦄ ≤ suc a → lim f ⦃ w ⦄ ≤ a
l≤p (inl r) = ns→≤ (l≤p-rd (inl (set r)))
```

## ω的性质

**定义 2-1-23**

```agda
instance
  fin-wf : wf fin
  fin-wf = zero₁

ω : Ord
ω = lim fin
```

**引理 2-1-24**

```agda
n<ω : fin n < ω
n<ω {n = zero}  = z<l
n<ω {n = suc n} = s<l n<ω
```

**引理 2-1-25**

```agda
n≤fn : ∀ f → ⦃ _ : wf f ⦄ → fin n ≤ f n
n≤fn {n = zero} f   = z≤
n≤fn {n = suc n} f  = begin
  fin (suc n)         ≤⟨ s≤s (n≤fn f) ⟩
  suc (f n)           ≤⟨ <→s≤ it ⟩
  f (suc n)           ∎ where open SubTreeReasoning
```

**推论 2-1-26**

```agda
n<fs : ∀ f n → ⦃ _ : wf f ⦄ → fin n < f (suc n)
n<fs f _ = ≤-<-trans (n≤fn f) it
```

**引理 2-1-27**

```agda
l≮ω : ⦃ IsLim a ⦄ → a ≮ ω
l≮ω {lim f} r = let n , r = lim-inv r in <-irrefl refl $ begin-strict
  fin n               ≤⟨ n≤fn f ⟩
  f n                 <⟨ f<l ⟩
  lim f               <⟨ r ⟩
  fin n               ∎ where open SubTreeReasoning
```

**引理 2-1-28**

```agda
ω≤l : ⦃ IsLim a ⦄ → ω < b → a < b → ω ≤ a
ω≤l {lim f} r s with <-connex r s
... | inl r           = inl r
... | inr (inr refl)  = inr refl
... | inr (inl r)     = ⊥-elim $ l≮ω r
```

**引理 2-1-29**

```agda
fin-inj : fin m ≡ fin n → m ≡ n
fin-inj {(zero)} {(zero)} eq = refl
fin-inj {suc m}  {suc n}  eq = cong suc $ fin-inj $ suc-inj eq
```

**引理 2-1-30**

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

**定理 2-1-31**

```agda
ℕ≡ω : ℕ ≡ Σ Ord (_< ω)
ℕ≡ω = pathToEq $ isoToPath $ iso
  (λ n → fin n , n<ω)
  (λ (a , a<ω) → fst (fin-suj a<ω))
  (λ a → ΣPathP $ eqToPath (snd $ fin-suj _) , toPathP (squash₁ _ _))
  (λ n → eqToPath $ fin-inj $ snd $ fin-suj _)
  where open import Cubical.Foundations.Isomorphism
```
