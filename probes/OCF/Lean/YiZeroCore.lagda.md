# YiZero 块：主线的块，零在顶之下

**判决：定义 (第 1 层)，没有定理。** 候选甲 (基本列向参照对齐) 的块。与 [YiLeanCore](YiLeanCore.lagda.md) 只差一处：第一位置里 `zero` 在 `top` 之下 (`Dn y a G.top = a ≡ G.zero`)，
因为 ω 倍改为从零起 (折叠在 [YiZeroFold](YiZeroFold.lagda.md))，极限的第 0 项是 0，第 1 项常是 `top`。其余照抄：层号 `LF` 有 Ω 结点，读回 `up`，塔 `tw`，`Λ`，加法 `plus`。
不否定主线。合法性在 [YiZeroLegal](YiZeroLegal.lagda.md)，塔合法在 [YiZeroTower](YiZeroTower.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroCore where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1 块

```agda
module G (P : Set) (L : P → Set) (K : Set) (B : K → Set) where
  data R : Set where
    zero : R
    suc  : R → R
    lim  : (ℕ → R) → R
    lc   : (r : P) (g : L r → R) → R
    em   : (i : K) → B i → R
    top  : R

data LF : Set

record Lay : Set₁ where
  constructor lay
  field
    A  : Set
    dn : A → A → Set
    lg : A → Set
    tp : A
    rd : A → LF

Pre : LF → Set
Lo : (x : LF) → Pre x → Lay
Kid : LF → Set
KS : (x : LF) → Kid x → Lay
Raw : LF → Set
layer : LF → Lay
Dn : (y : LF) → Raw y → Raw y → Set
DnI : (y : LF) (i j : Kid y) → i ≡ j → Lay.A (KS y i) → Lay.A (KS y j) → Set
Lgl : (y : LF) → Raw y → Set
up : (y : LF) → Raw y → LF
upN : (y : LF) (r : Pre y) → (Lay.A (Lo y r) → LF) → LF
upT : LF → LF

data LF where
  zero : LF
  suc  : LF → LF
  lim  : (ℕ → LF) → LF
  lc   : (k : LF) (g : Raw k → LF) → LF

Raw x = G.R (Pre x) (λ r → Lay.A (Lo x r)) (Kid x) (λ i → Lay.A (KS x i))

layer k = lay (Raw k) (Dn k) (Lgl k) G.top (up k)

Pre zero = ⊥
Pre (suc k) = ⊤ ⊎ Pre k
Pre (lim f) = Σ ℕ λ n → Pre (f n)
Pre (lc k g) = Σ (Raw k) λ η → Lgl k η × Pre (g η)

Lo zero ()
Lo (suc k) (inj₁ _) = layer k
Lo (suc k) (inj₂ r) = Lo k r
Lo (lim f) (n , r) = Lo (f n) r
Lo (lc k g) (η , _ , r) = Lo (g η) r

Kid zero = ⊥
Kid (suc k) = ⊤
Kid (lim f) = ℕ
Kid (lc k g) = Σ (Raw k) (Lgl k)

KS zero ()
KS (suc k) _ = layer k
KS (lim f) n = layer (f n)
KS (lc k g) (η , _) = layer (g η)
```

`Dn` 的最后一行是这里与主线不同的地方：`top` 的严格第一位置只有 `zero`。

```agda
Le : (X : Lay) → Lay.A X → Lay.A X → Set
Le X a d = (a ≡ d) ⊎ Lay.dn X a d

Cp : (y : LF) → Raw y → Raw y → Set
Cp y a d = (a ≡ d) ⊎ Dn y a d

Dn y a G.zero = ⊥
Dn y a (G.suc d) = Cp y a d
Dn y a (G.lim f) = Σ ℕ λ n → Cp y a (f n)
Dn y a (G.lc r g) = Cp y a (g (Lay.tp (Lo y r)))
Dn y (G.em i a) (G.em j d) = Σ (i ≡ j) λ q → DnI y i j q a d
Dn y a (G.em j d) = ⊥
Dn y a G.top = a ≡ G.zero

DnI y i .i refl a d = Lay.dn (KS y i) a d

Lgl y G.zero = ⊤
Lgl y (G.suc a) = Lgl y a
Lgl y (G.lim f) = (∀ n → Cp y (f n) (f (suc n))) × (∀ n → Lgl y (f n))
Lgl y (G.lc r g) =
  (∀ η → Lay.lg (Lo y r) η → Lgl y (g η)) ×
  (∀ η η′ → Lay.lg (Lo y r) η → Le (Lo y r) η η′ → Lay.lg (Lo y r) η′ → Cp y (g η) (g η′))
Lgl y (G.em i a) = Lay.lg (KS y i) a
Lgl y G.top = ⊤
```

## 2 读回与塔

```agda
up y G.zero = zero
up y (G.suc a) = suc (up y a)
up y (G.lim f) = lim (λ n → up y (f n))
up y (G.lc r g) = upN y r (λ η → up y (g η))
up y (G.em i a) = Lay.rd (KS y i) a
up y G.top = upT y

upN zero ()
upN (suc k) (inj₁ _) h = lc k h
upN (suc k) (inj₂ r) h = upN k r h
upN (lim f) (n , r) h = upN (f n) r h
upN (lc k g) (η , _ , r) h = upN (g η) r h

upT zero = suc zero
upT (suc k) = lc k (up k)
upT (lim f) = lim (λ n → upT (f n))
upT (lc k g) = lc k (λ η → upT (g η))

tw : ℕ → LF
tw zero = zero
tw (suc n) = upT (tw n)

Λ : LF
Λ = lim tw
```

## 3 一般层的加法

照抄主线：`x + y` 把 `x` 放在 `y` 的叶上。

```agda
acc : ∀ {T : Set} → (ℕ → T → T) → T → ℕ → T
acc s x zero = x
acc s x (suc n) = s n (acc s x n)

Bld : LF → LF → Set
Bld M k = (r : Pre k) → (Lay.A (Lo k r) → Raw M) → Raw M

add : ∀ {M} k → Bld M k → Raw M → Raw k → Raw M
add k B x G.zero = x
add k B x (G.suc a) = G.suc (add k B x a)
add k B x (G.lim f) = G.lim (λ n → add k B x (f n))
add k B x (G.lc r g) = B r (λ η → add k B x (g η))
add zero B x (G.em () a)
add (suc k) B x (G.em _ a) = add k (λ r → B (inj₂ r)) x a
add (lim f) B x (G.em n a) = add (f n) (λ r → B (n , r)) x a
add (lc j g) B x (G.em (η , l) a) = add (g η) (λ r → B (η , l , r)) x a
add zero B x G.top = G.suc x
add (suc k) B x G.top = B (inj₁ tt) (λ η → add k (λ r → B (inj₂ r)) x η)
add (lim f) B x G.top =
  G.lim (λ n → acc (λ i y → add (f i) (λ r → B (i , r)) y G.top) x (suc n))
add (lc j g) B x G.top = G.suc x

plus : ∀ m → Raw m → Raw m → Raw m
plus m = add m G.lc
```
