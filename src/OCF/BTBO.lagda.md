# 形式化大数数学 (3.0 - 布劳威尔树壁垒序数)

> 交流Q群: 893531731  
> 本文源码: [BTBO.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/OCF/BTBO.lagda.md)  
> 高亮渲染: [BTBO.html](https://choukh.github.io/agda-googology/OCF.BTBO.html)  
> 纯代码版: [BTBO.agda](https://gist.github.com/choukh/d7ca58dd90ee112162debce78eb7ad78)

我们主张的形式化大数基于以下纲领:

1. 序数先行
   - 先实现序数再折叠成大数
   - 排除很难分析序数上下界的函数以及非序数增长率函数
2. 理想计算机可运行
   - 在以类型论为基础的证明助理中无公理地写出定义
3. 保证停机
   - 通过证明助理的自动停机检查器保证停机

本文可能是该系列的最后一篇, 因为遵循该纲领, 我们目前卡在了 $\psi(\Omega_\Omega)$. 为了引起重视, 我们将其命名为布劳威尔树壁垒序数 (Brouser Tree Barrier Ordinal), 简称 BTBO. 本文将介绍该序数的实现.

```agda
{-# OPTIONS --safe --lossy-unification #-}
module OCF.BTBO where
```

```agda
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; it)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)

transport : {A B : Set} → A ≡ B → A → B
transport refl x = x

module ℕ where
  open import Data.Nat using (ℕ; zero; suc) public
  variable n m : ℕ

  iter : {T : Set} (f : T → T) (init : T) (times : ℕ) → T
  iter f a zero    = a
  iter f a (suc n) = f (iter f a n)

  data _<_ : ℕ → ℕ → Set where
    zero : n < suc n
    suc  : n < m → n < suc m

  z<s : ∀ n → zero < suc n
  z<s zero    = zero
  z<s (suc n) = suc (z<s n)

  s<s : n < m → suc n < suc m
  s<s zero      = zero
  s<s (suc p)  = suc (s<s p)

  <-dec : ∀ n m → n < m ⊎ m < n ⊎ n ≡ m
  <-dec zero zero = injᶜ refl
  <-dec zero (suc m) = injᵃ (z<s m)
  <-dec (suc n) zero = injᵇ (z<s n)
  <-dec (suc n) (suc m) with <-dec n m
  ... | injᵃ p = injᵃ (s<s p)
  ... | injᵇ p = injᵇ (s<s p)
  ... | injᶜ p = injᶜ (cong suc p)

open ℕ using (ℕ; zero; suc)

module Ordᴰ where
  infix 10 _<_
  data Ordᴰ : Set
  data _<_ : Ordᴰ → Ordᴰ → Set

  monotonic : (ℕ → Ordᴰ) → Set
  monotonic f = ∀ {n m} → n ℕ.< m → f n < f m

  private variable
    a b c : Ordᴰ
    f :  ℕ → Ordᴰ
    mono : monotonic f

  data Ordᴰ where
    zero : Ordᴰ
    suc  : Ordᴰ → Ordᴰ
    lim  : (f : ℕ → Ordᴰ) (mono : monotonic f) → Ordᴰ

  data _<_ where
    zero : a < suc a
    suc  : a < b → a < suc b
    lim  : ∀ n → a < f n → a < lim f mono

  f<l : ∀ n → f n < lim f mono
  f<l {mono} n = lim (suc n) (mono zero)

  <-trans : a < b → b < c → a < c
  <-trans p zero      = suc p
  <-trans p (suc q)   = suc (<-trans p q)
  <-trans p (lim n q) = lim n (<-trans p q)

  <-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b
  <-dec zero zero       = injᶜ refl
  <-dec zero (suc q)    = injᵇ q
  <-dec (suc p) zero    = injᵃ p
  <-dec (suc p) (suc q) = <-dec p q
  <-dec (lim {mono} n p) (lim m q) with ℕ.<-dec n m
  ... | injᵃ n<m  = <-dec (<-trans p (mono n<m)) q
  ... | injᵇ m<n  = <-dec p (<-trans q (mono m<n))
  ... | injᶜ refl = <-dec p q

  mutual
    _+_ : Ordᴰ → Ordᴰ → Ordᴰ
    a + zero          = a
    a + suc b         = suc (a + b)
    a + lim f f-mono  = lim (λ n → a + f n) (+-mono ∘ f-mono)

    +-mono : b < c → a + b < a + c
    +-mono zero       = zero
    +-mono (suc p)    = suc (+-mono p)
    +-mono (lim n p)  = lim n (+-mono p)

  NonZero : Ordᴰ → Set
  NonZero zero = ⊥
  NonZero _    = ⊤

  sth<nz : a < b → NonZero b
  sth<nz zero       = _
  sth<nz (suc _)    = _
  sth<nz (lim _ _)  = _

  z<nz : NonZero a → zero < a
  z<nz {suc zero}         _ = zero
  z<nz {suc (suc a)}      _ = suc (z<nz _)
  z<nz {suc (lim f mono)} _ = suc (z<nz _)
  z<nz {lim f mono}       _ = lim 1 (z<nz (sth<nz (mono zero)))

  a<a+b : ⦃ _ : NonZero b ⦄ → a < a + b
  a<a+b = +-mono (z<nz it)

  -- cumulative sum
  cumsum : (ℕ → Ordᴰ) → (ℕ → Ordᴰ)
  cumsum f zero     = f zero
  cumsum f (suc n)  = cumsum f n + suc (f (suc n))

  cumsum-mono : (f : ℕ → Ordᴰ) → monotonic (cumsum f)
  cumsum-mono f zero    = a<a+b
  cumsum-mono f (suc p) = <-trans (cumsum-mono f p) a<a+b

open Ordᴰ hiding (_+_)
private variable i ℓ ℓ₁ ℓ₂ : Ordᴰ

module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
  data Ord₊ : Set where
    zero  : Ord₊
    suc   : Ord₊ → Ord₊
    lim   : (f : ℕ → Ord₊) → Ord₊
    limₗ  : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊

Ord< : (i : Ordᴰ) (p : i < ℓ) → Set
Ord< i zero      = Ord₊ i Ord<
Ord< i (suc p)   = Ord< i p
Ord< i (lim n p) = Ord< i p

Ord : Ordᴰ → Set
Ord ℓ = Ord< ℓ zero

Ord₀ : Set
Ord₀ = Ord zero

Ord<-≡ : (p : i < ℓ₁) (q : i < ℓ₂) → Ord< i p ≡ Ord< i q
Ord<-≡ zero zero      = refl
Ord<-≡ (suc p) zero   = Ord<-≡ p zero
Ord<-≡ (lim n p) zero = Ord<-≡ p zero
Ord<-≡ p (suc q)      = trans (Ord<-≡ p q) refl
Ord<-≡ p (lim n q)    = trans (Ord<-≡ p q) refl

coe : {p : i < ℓ₁} {q : i < ℓ₂} → Ord< i p → Ord< i q
coe {p} {q} = transport (Ord<-≡ p q)

coe₀ : {p : i < ℓ₂} → Ord i → Ord< i p
coe₀ = coe {p = zero}

↑₀ : ℕ → Ord₀
↑₀ zero = zero
↑₀ (suc n) = suc (↑₀ n)

↑ : ℓ₁ < ℓ₂ → Ord ℓ₁ → Ord ℓ₂
↑ p zero        = zero
↑ p (suc a)     = suc (↑ p a)
↑ p (lim f)     = lim (↑ p ∘ f)
↑ p (limₗ q f)  = limₗ (<-trans q p) (↑ p ∘ f ∘ coe)

Ω : (ℓ : Ordᴰ) → Ord ℓ
Ω zero          = lim ↑₀
Ω (suc ℓ)       = limₗ zero (↑ zero)
Ω (lim f mono)  = lim (λ n → ↑ (f<l n) (Ω (f n)))

iter : (f : Ord ℓ → Ord ℓ) (init : Ord ℓ) (times : Ord ℓ) → Ord ℓ
iter f a zero       = a
iter f a (suc b)    = f (iter f a b)
iter f a (lim g)    = lim (iter f a ∘ g)
iter f a (limₗ p g) = limₗ p (iter f a ∘ g)

_+_ _*_ _^_ : Ord ℓ → Ord ℓ → Ord ℓ
_+_ a = iter suc a
_*_ a = iter (_+ a) zero
_^_ a = iter (_* a) (suc zero)

lfp : (Ord ℓ → Ord ℓ) → Ord ℓ
lfp f = lim (ℕ.iter f zero)

ψ< : i < ℓ → Ord ℓ → Ord i
ψ< p zero     = lfp (Ω _ ^_)
ψ< p (suc a)  = lfp (ψ< p a ^_)
ψ< p (lim f)  = lim (ψ< p ∘ f)
ψ< {i} {ℓ} p (limₗ {i = j} q f) with <-dec q p
... | injᵃ j<i  = limₗ j<i (ψ< p ∘ f ∘ coe)
... | injᵇ i<j  = lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)
... | injᶜ refl = lfp (ψ< p ∘ f ∘ coe₀)

ψ₀ : Ord ℓ → Ord₀
ψ₀ {ℓ = zero}       a = a
ψ₀ {ℓ = suc ℓ}      a = ψ₀ (ψ< zero a)
ψ₀ {ℓ = lim f mono} a = lim (λ n → ψ₀ (ψ< (f<l n) a))

ordᴰ : Ord₀ → Ordᴰ
ordᴰ zero     = zero
ordᴰ (suc a)  = suc (ordᴰ a)
ordᴰ (lim f)  = lim (cumsum (ordᴰ ∘ f)) (cumsum-mono (ordᴰ ∘ f))

-- n-iteration of ψ₀
ψⁿ : ℕ → Ord₀
ψⁿ = ℕ.iter (ψ₀ ∘ Ω ∘ ordᴰ) zero

ex1 = ψⁿ 1    -- ω
ex2 = ψⁿ 2    -- Buchholz's ordinal
ex3 = ψⁿ 3    -- ψ(Ω_BO)
ex4 = ψⁿ 4    -- ψ(Ω_ψ(Ω_BO))

BTBO : Ord₀
BTBO = lim ψⁿ -- ψ(Ω_Ω)

FGH : Ord₀ → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = ℕ.iter (FGH a) n n
FGH (lim a) n = FGH (a n) n

mynum : ℕ
mynum = FGH BTBO 99
```

## 参考

- [Andras Kovacs - Large countable ordinals and numbers in Agda](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a?permalink_comment_id=5617267)
- [ccz181078 - googology](https://github.com/ccz181078/googology)
- [Thierry Coquand - Inductive Definitions and Constructive Mathematics](https://www.cse.chalmers.se/~coquand/prague1.pdf)
- [Googology Wiki - Ordinal collapsing function](https://googology.fandom.com/wiki/Ordinal_collapsing_function)
- [ユーザーブログ:Hexirp - ブラウワー順序数の制限と拡張](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/ブラウワー順序数の制限と拡張)
- [ユーザーブログ:Hexirp - 2024-12-25 のメモ](https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/2024-12-25_のメモ)
