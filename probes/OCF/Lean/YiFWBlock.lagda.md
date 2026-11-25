# B7 候选：带分支结构等价的第一位置
> 原型，未接主线。来源：旧 `YiRC-RCE` 的一层块与加法；新增带第一点的关系同构，且要求槽位所在层相等。
> 新子句只消费等价证据，不判定等价；良基在 `YiFWWf`，旧块兼容在 `YiFWCompat`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFWBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- 分支类型带第一点及关系；等价同时搬运这三项。
record Iso₀ (X Y : Set) (x₀ : X) (y₀ : Y)
            (RX : X → X → Set) (RY : Y → Y → Set) : Set where
  field
    cv : Y → X
    back : X → Y
    cv-back : ∀ x → cv (back x) ≡ x
    back-cv : ∀ y → back (cv y) ≡ y
    first : cv y₀ ≡ x₀
    forward : ∀ {a b} → RY a b → RX (cv a) (cv b)
    backward : ∀ {a b} → RX a b → RY (back a) (back b)

record Sg : Set₁ where
  constructor sg
  field
    P : Set
    B : P → Set
    C : Set
    D : C → Set
    b₀ : (p : P) → B p
    z₀ : (c : C) → D c
    R : (c : C) → D c → D c → Set
    Lv : Set
    lev : P → Lv
    Q : (p : P) → B p → B p → Set
open Sg public

E : (S : Sg) → P S → P S → Set
E S p q = Σ (lev S p ≡ lev S q) λ _ → Iso₀ (B S p) (B S q) (b₀ S p) (b₀ S q) (Q S p) (Q S q)

cv : ∀ S {p q} → E S p q → B S q → B S p
cv S e = Iso₀.cv (proj₂ e)

cv₀ : ∀ S {p q} (e : E S p q) → cv S e (b₀ S q) ≡ b₀ S p
cv₀ S e = Iso₀.first (proj₂ e)

reflE : ∀ S p → E S p p
reflE S p = refl , record
  { cv = λ x → x ; back = λ x → x
  ; cv-back = λ _ → refl ; back-cv = λ _ → refl
  ; first = refl ; forward = λ d → d ; backward = λ d → d }

mutual
  data T (S : Sg) : Set where
    zero : T S
    suc  : T S → T S
    lim  : (f : ℕ → T S) → ((n : ℕ) → Lt S (f n) (f (suc n))) → T S
    Ω    : (p : P S) → (B S p → T S) → T S
    up   : T S → (c : C S) (y : D S c) → R S c (z₀ S c) y → T S

  data Lt (S : Sg) : T S → T S → Set where
    ◃s : ∀ {x} → Lt S x (suc x)
    ◃l : ∀ {f a} (n : ℕ) → Lt S (f n) (lim f a)
    ◃w : ∀ {p g} → Lt S (g (b₀ S p)) (Ω p g)
    ◃u : (x : T S) (c : C S) (y : D S c) (e : R S c (z₀ S c) y) → Lt S x (up x c y e)
    ◃c : (x : T S) (c : C S) {y′ y : D S c} {e′ : R S c (z₀ S c) y′} {e : R S c (z₀ S c) y}
       → R S c y′ y → Lt S (up x c y′ e′) (up x c y e)
    ◃t : ∀ {x y z} → Lt S x y → Lt S y z → Lt S x z
    -- 新子句: 同层号不同槽位的两个结点, 分支在结构等价下逐点是第一位置
    ◃σ : ∀ {p p′ g g′} (e : E S p p′) → ((z : B S p′) → Lt S (g (cv S e z)) (g′ z)) → Lt S (Ω p g) (Ω p′ g′)

-- 一层之内的运算照旧可写, 各多一个子句
module _ {S : Sg} where
  infixl 6 _+_
  mutual
    _+_ : T S → T S → T S
    x + zero       = x
    x + suc y      = suc (x + y)
    x + lim f a    = lim (λ n → x + f n) (λ n → +-mono x (a n))
    x + Ω p g      = Ω p (λ z → x + g z)
    x + up y c w e = up (x + y) c w e

    +-mono : (c : T S) {a b : T S} → Lt S a b → Lt S (c + a) (c + b)
    +-mono c ◃s           = ◃s
    +-mono c (◃l n)       = ◃l n
    +-mono c ◃w           = ◃w
    +-mono c (◃u x k y e) = ◃u (c + x) k y e
    +-mono c (◃c x k d)   = ◃c (c + x) k d
    +-mono c (◃t d e)     = ◃t (+-mono c d) (+-mono c e)
    +-mono c (◃σ e h)     = ◃σ e (λ z → +-mono c (h z))

  -- 新子句不破坏 "之下有零": 结点的第一分支仍在结点之下
  σ-first : ∀ {p p′} (g : B S p → T S) (g′ : B S p′ → T S) (e : E S p p′) → ((z : B S p′) → Lt S (g (cv S e z)) (g′ z)) → Lt S (g (b₀ S p)) (Ω p′ g′)
  σ-first {p} {p′} g g′ e h = ◃t (subst (λ t → Lt S (g t) (g′ (b₀ S p′))) (cv₀ S e) (h (b₀ S p′))) ◃w


open import Data.Empty using (⊥)

no-zero : ∀ {S x} → Lt S x zero → ⊥
no-zero (◃t d e) = no-zero e
```
