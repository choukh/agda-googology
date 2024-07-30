---
title: 形式化大数数学 (2.1 - 良构树序数的性质)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.1 - 良构树序数的性质)

> 交流Q群: 893531731  
> 本文源码: [Properties.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Properties.lagda.md)  
> 高亮渲染: [Properties.html](https://choukh.github.io/agda-googology/WellFormed.Properties.html)  

```agda
{-# OPTIONS --safe --cubical #-}
module WellFormed.Properties where
open import WellFormed.Base
```

[上一篇](https://zhuanlan.zhihu.com/p/711649863)我们定义了良构树序数并证明了一些基本性质, 本文将继续讨论它的更多性质.

## 序数函数

我们先定义序数函数的一些性质.

**定义 2-1-0** 我们把序数函数的类型简记作 $\text{Func}$, 序数的二元关系的类型简记作 $\text{Rel}$, 并约定今后都用大写的 $F$ 表示序数函数.

```agda
Func : Type
Func = Ord → Ord
variable F : Func

Rel : Type₁
Rel = Ord → Ord → Type
```

**定义 2-1-1** 我们说一个序数函数 $F$ **膨胀**一个序数关系 $\sim$, 当且仅当对任意序数 $x$ 都有 $x \sim F(x)$.

```agda
_inflates_ : Func → Rel → Type
F inflates _~_ = ∀ {x} → x ~ F x
```

**事实 2-1-2** 如果 $F$ 膨胀 $\lt$, 那么 $F$ 膨胀 $\leq$.

```agda
infl<→infl≤ : F inflates _<_ → F inflates _≤_
infl<→infl≤ p = <→≤ p
```

**定义 2-1-3** 我们说一个序数函数 $F$ **保持**一个序数关系 $\sim$, 当且仅当对任意序数 $x, y$ 都有 $x \sim y \to F(x) \sim F(y)$.

```agda
_preserves_ : Func → Rel → Type
F preserves _~_ = ∀ {x y} → x ~ y → F x ~ F y
```

**事实 2-1-4** 如果 $F$ 保持 $\lt$, 那么 $F$ 保持 $\leq$.

```agda
pres<→pres≤ : F preserves _<_ → F preserves _≤_
pres<→pres≤ pres (inl p)    = <→≤ (pres p)
pres<→pres≤ pres (inr refl) = inr refl
```

**定义 2-1-5** 我们说一个序数函数 $F$ **单射**一个序数关系 $\sim$, 当且仅当对任意序数 $x, y$ 都有 $F(x) \sim F(y) \to x \sim y$.

```agda
_injects_ : Func → Rel → Type
F injects _~_ = ∀ {x y} → F x ~ F y → x ~ y
```

**事实 2-1-6** 如果 $F$ 单射 $\lt$, 那么 $F$ 单射 $\leq$.

```agda
inj<→inj≤ : F injects _≡_ → F injects _<_ → F injects _≤_
inj<→inj≤ inj inj< (inl p) = inl (inj< p)
inj<→inj≤ inj inj< (inr p) = inr (inj p)
```

**定义 2-1-7** 我们说一个保持 $\lt$ 的序数函数 $F$ 是**连续**的, 当且仅当对任意良构序列 $f$ 都有 $F(\lim f) = \lim (F \circ f)$.

```agda
continuous : F preserves _<_ → Type
continuous {F} pres = ∀ {f} ⦃ _ : wf f ⦄ → F (lim f) ≡ lim (F ∘ f) ⦃ pres it ⦄
```

**注意 2-1-8** 在传统定义中「保持 $\lt$」与「连续」分开的, 但在我们这套定义中只有保持 $\lt$ 的函数才可以谈论是否连续, 因为受良构条件约束.

**定义 2-1-9** 我们说一个序数函数 $F$ 是**正规**的, 当且仅当它保持 $\lt$ 且连续.

```agda
record Normal : Type where
  constructor normal
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<
```

## 一些约定

**定义** 自然数到序数的嵌入 $\text{fin} : ℕ → \text{Ord}$

$$
\text{fin}~n := \text{suc}^n~0
$$

其中后继函数的上标 $n$ 表示迭代 $n$ 次.

```agda
open import Lower public using (_∘ⁿ_)
fin : Seq
fin n = (suc ∘ⁿ n) zero
```

**约定** 数字字面量既可以表示自然数, 也可以表示序数. Agda 使用[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能实现该约定.

```agda
open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }
```

**约定** 我们将 $\text{suc}(\text{suc}(a))$ 记作 $a^{++}$.

```agda
pattern 2+ a = suc (suc a)
```

**约定** 非零序数指不等于零的序数.

```agda
not0 : Ord → Type
not0 zero = ⊥
not0 _ = ⊤

record NonZero (a : Ord) : Type where
  field nonZero : not0 a

nz-intro-rd : Road 0 a → NonZero a
nz-intro-rd {suc _} _ = _
nz-intro-rd {lim _} _ = _

nz-intro : 0 < a → NonZero a
nz-intro = nz-intro-rd ∘ set
```

**约定** 非平凡序数指不等于零或一的序数.

```agda
not01 : Ord → Type
not01 zero       = ⊥
not01 (suc zero) = ⊥
not01 _          = ⊤

record NonTrivial (a : Ord) : Type where
  field nonTrivial : not01 a

nt-intro-rd : Road 1 a → NonTrivial a
nt-intro-rd {suc zero} (suc ())
nt-intro-rd {2+ a}         _ = _
nt-intro-rd {suc (lim _)}  _ = _
nt-intro-rd {lim _}        _ = _

nt-intro : 1 < a → NonTrivial a
nt-intro = nt-intro-rd ∘ set
```
