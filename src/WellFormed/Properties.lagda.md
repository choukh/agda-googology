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

我们先定义序数函数的一些性质.

**定义 2-1-0** 我们把序数函数的类型简记作 $\text{Func}$, 序数的二元关系的类型简记作 $\text{Rel}$, 并约定今后都用大写的 $F$ 表示序数函数.

```agda
Func : Type
Func = Ord → Ord
variable F : Func

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
pres<→pres≤ : F preserves _<_ → F preserves _≤_
pres<→pres≤ pres (inl p)    = <→≤ (pres p)
pres<→pres≤ pres (inr refl) = inr refl
```

**定义 2-1-3** 我们说一个序数函数 $F$ **单射**一个序数关系 $\sim$, 当且仅当对任意序数 $x, y$ 都有 $F(x) \sim F(y) \to x \sim y$.

```agda
_injects_ : Func → Rel → Type
F injects _~_ = ∀ {x y} → F x ~ F y → x ~ y
```

**事实 2-1-4** 如果 $F$ 单射 $\lt$, 那么 $F$ 单射 $\leq$.

```agda
inj<→inj≤ : F injects _≡_ → F injects _<_ → F injects _≤_
inj<→inj≤ inj inj< (inl p) = inl (inj< p)
inj<→inj≤ inj inj< (inr p) = inr (inj p)
```

## 一些约定

**定义 2-1-5** 自然数到序数的嵌入 $\text{fin} : ℕ → \text{Ord}$

$$
\text{fin}(n) := \text{suc}^n(0)
$$

其中后继函数的上标 $n$ 表示迭代 $n$ 次.

```agda
open import Lower public using (_∘ⁿ_)
fin : Seq
fin n = (suc ∘ⁿ n) zero
```

**约定 2-1-6** 数字字面量既可以表示自然数, 也可以表示序数. Agda 使用[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能实现该约定.

```agda
open import Agda.Builtin.FromNat public
instance
  nNat = Number ℕ   ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nOrd = Number Ord ∋ record { Constraint = λ _ → ⊤ ; fromNat = λ n → fin n }
```

## 一些引理

**事实 2-1-7** 构造子的单射性

```agda
suc-inj : suc a ≡ suc b → a ≡ b
suc-inj refl = refl

lim-inj : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → Ord.lim f ≡ lim g → f ≡ g
lim-inj refl = refl
```

**事实 2-1-8** 极限路径的反演

```agda
lim-inv-rd : ⦃ _ : wf f ⦄ → Road a (lim f) → Σ[ n ∈ ℕ ] Road a (f n)
lim-inv-rd (lim r) = _ , r

lim-inv : ⦃ _ : wf f ⦄ → a < lim f → Σ[ n ∈ ℕ ] a < f n
lim-inv r with lim-inv-rd (set r)
... | n , r = n , ∣ r ∣₁
```

**定理 2-1-9**

```agda
z<b-rd : Road a b → Road 0 b
z<s-rd : Road 0 (suc a)

z<b : a < b → 0 < b
z<b = map z<b-rd

z<s : 0 < suc a
z<s = ∣ z<s-rd ∣₁
```

**引理 2-1-9-1**

```agda
z<l-rd : ⦃ _ : wf f ⦄ → Road 0 (lim f)
z<l-rd = lim {n = 1} (z<b-rd (set it))

z<l : ⦃ _ : wf f ⦄ → 0 < lim f
z<l = ∣ z<l-rd ∣₁
```

**引理 2-1-9-2**

```agda
z<fs-rd : ∀ f n → ⦃ _ : wf f ⦄ → Road 0 (f (suc n))
z<fs-rd _ _ = z<b-rd (set it)

z<fs : ∀ f n → ⦃ _ : wf f ⦄ → 0 < f (suc n)
z<fs f n = ∣ z<fs-rd f n ∣₁
```

**引理 2-1-9-3**

```agda
z<b-rd zero = z<s-rd
z<b-rd (suc r) = z<s-rd
z<b-rd (lim r) = z<l-rd
```

**引理 2-1-9-4**

```agda
z<s-rd {(zero)} = zero
z<s-rd {suc a} = suc z<s-rd
z<s-rd {lim f} = suc (lim (z<fs-rd f 1))
```

**推论 2-1-10**

```agda
z≤ : 0 ≤ a
z≤ {(zero)} = inr refl
z≤ {suc _}  = inl z<s
z≤ {lim _}  = inl z<l
```

**定理 2-1-11** 后继运算的保序性

```agda
<→s≤-rd : Road a b → NSRoad (suc a) b
s<s-rd : suc preserves Road

<→s≤ : a < b → suc a ≤ b
<→s≤ = rec isProp≤ (ns→≤ ∘ <→s≤-rd)

s<s : suc preserves _<_
s<s = map s<s-rd
```

**引理 2-1-11-1**

```agda
<→s≤-rd zero = inr refl
<→s≤-rd (suc r) = inl (s<s-rd r)
<→s≤-rd {a} (lim {f} {n} r) = inl $ lim $ begin-strict
  suc a           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd (set it) ⟩
  f (suc n)       ∎ where open RoadReasoning
```

**引理 2-1-11-2**

```agda
s<s-rd zero = zero
s<s-rd (suc r) = suc (s<s-rd r)
s<s-rd {x} (lim {f} {n} r) = suc $ begin-strict
  suc x           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd f<l-rd ⟩
  lim f           ∎ where open RoadReasoning
```

**推论 2-1-12**

```agda
s<s-inj-rd : suc injects Road
s<s-inj-rd zero = zero
s<s-inj-rd (suc r) = rd-trans zero r

s<s-inj : suc injects _<_
s<s-inj = map s<s-inj-rd
```

**定理 2-1-13**

```agda
s≤→<-rd : NSRoad (suc a) b → Road a b
s≤→<-rd {b = suc b} (inl r)       = suc (s<s-inj-rd r)
s≤→<-rd {b = suc b} (inr refl)    = zero
s≤→<-rd {b = lim f} (inl (lim r)) = lim (rd-trans zero r)

s≤→< : suc a ≤ b → a < b
s≤→< (inl r)    = map (s≤→<-rd ∘ inl) r
s≤→< (inr refl) = zero₁
```

**推论 2-1-14**

```agda
s≤s : suc preserves _≤_
s≤s = pres<→pres≤ s<s

s≤s-inj : suc injects _≤_
s≤s-inj = inj<→inj≤ suc-inj s<s-inj
```

**定理 2-1-15**

```agda
s<l-rd : ⦃ _ : wf f ⦄ → Road a (lim f) → Road (suc a) (lim f)
s<l-rd {a} (lim {f} {n} r) = begin-strict
  suc a           <⟨ s<s-rd r ⟩
  suc (f n)       ≤⟨ <→s≤-rd f<l-rd ⟩
  lim f           ∎ where open RoadReasoning

s<l : ⦃ _ : wf f ⦄ → a < lim f → suc a < lim f
s<l = map s<l-rd
```

**定理 2-1-16**

```agda
l≤p-rd : ⦃ _ : wf f ⦄ → NSRoad (lim f) (suc a) → NSRoad (lim f) a
l≤p-rd (inl zero)    = inr refl
l≤p-rd (inl (suc r)) = inl r

l≤p : ⦃ _ : wf f ⦄ → lim f ≤ suc a → lim f ≤ a
l≤p (inl r) = ns→≤ (l≤p-rd (inl (set r)))
```

## ω的性质

**定义 2-1-17**

```agda
instance
  fin-wf : wf fin
  fin-wf = zero₁

ω : Ord
ω = lim fin
```

**引理 2-1-18**

```agda
n<ω : fin n < ω
n<ω {n = zero}  = z<l
n<ω {n = suc n} = s<l n<ω
```

**引理 2-1-19**

```agda
n≤fn : ∀ f → ⦃ _ : wf f ⦄ → fin n ≤ f n
n≤fn {n = zero} f   = z≤
n≤fn {n = suc n} f  = begin
  fin (suc n)         ≤⟨ s≤s (n≤fn f) ⟩
  suc (f n)           ≤⟨ <→s≤ it ⟩
  f (suc n)           ∎ where open SubTreeReasoning
```

**推论 2-1-20**

```agda
n<fs : ∀ f n → ⦃ _ : wf f ⦄ → fin n < f (suc n)
n<fs f _ = ≤-<-trans (n≤fn f) it
```

**引理 2-1-21**

```agda
l≮ω : ⦃ _ : wf f ⦄ → lim f ≮ ω
l≮ω {f} r = let n , r = lim-inv r in <-irrefl refl $ begin-strict
  fin n               ≤⟨ n≤fn f ⟩
  f n                 <⟨ f<l ⟩
  lim f               <⟨ r ⟩
  fin n               ∎ where open SubTreeReasoning
```

**引理 2-1-22**

```agda
ω≤l : ⦃ _ : wf f ⦄ → ω < a → lim f < a → ω ≤ lim f
ω≤l {f} r s with <-connex r s
... | inl r           = inl r
... | inr (inr refl)  = inr refl
... | inr (inl r)     = ⊥-elim $ l≮ω r
```

**引理 2-1-23**

```agda
fin-inj : fin m ≡ fin n → m ≡ n
fin-inj {(zero)} {(zero)} eq = refl
fin-inj {suc m}  {suc n}  eq = cong suc $ fin-inj $ suc-inj eq
```

**引理 2-1-24**

```agda
fin-suj : a < ω → Σ[ n ∈ ℕ ] fin n ≡ a
fin-suj {(zero)} r  = 0 , refl
fin-suj {suc _}  r  with fin-suj (<-trans zero₁ r)
... | n , refl      = suc n , refl
fin-suj {lim f}  r  = ⊥-elim $ <-irrefl refl $ begin-strict
  ω                 ≤⟨ ω≤l zero₁ (<-trans r zero₁) ⟩
  lim f             <⟨ r ⟩
  ω                 ∎ where open SubTreeReasoning
```

**定理 2-1-25**

```agda
ℕ≡ω : ℕ ≡ Σ Ord (_< ω)
ℕ≡ω = pathToEq $ isoToPath $ iso
  (λ n → fin n , n<ω)
  (λ (a , a<ω) → fst (fin-suj a<ω))
  (λ a → ΣPathP $ eqToPath (snd $ fin-suj _) , toPathP (squash₁ _ _))
  (λ n → eqToPath $ fin-inj $ snd $ fin-suj _)
  where open import Cubical.Foundations.Isomorphism
```
