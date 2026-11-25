# 合法性进块: 块

> 判决: 成品候选 (块, 原型). 一层的树 `T` 与第一位置序 `Lt` 归纳-归纳地一起定义: ℕ 极限自带相邻项的步进, 嵌入自带 "孩子非零", 所以每棵树都合法, 没有另外的合法性谓词.
> 层号 `L` 与各层的树 `Tr` 归纳-递归; `Ωₗ k h` 的 `h`, Ω 结点的分支, `Ωₗ` 的孩子下标都取在 `Tr k` 上, 即只在低层合法树上 (纲领第 1 条).
> 不否定什么. 对照: 合法性作 Σ 的写法检查器也接受 (`YiLegBlockSigma`). 运算在 `YiLegOps`, 路径与证据在 `YiLegPath`, 折叠在 `YiLegFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 一层的树与它的序

参数: 槽位 `P`, 分支类型 `B`, 孩子 `C`, 孩子层的树 `D`, 每个槽位的第一分支 `b₀`, 孩子层的零 `z₀`, 孩子层的序 `R`.
`◃u`, `◃c` 的 x 写成显式参数: 折叠与单调性互递归时, 检查器要看到 x 是推导的子项.

```agda
record Sg : Set₁ where
  constructor sg
  field
    P  : Set
    B  : P → Set
    C  : Set
    D  : C → Set
    b₀ : (p : P) → B p
    z₀ : (c : C) → D c
    R  : (c : C) → D c → D c → Set
open Sg public

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
```

## 层号与各层的树

与 `YiFreshBlock` 同一个结; 多出的三个递归函数 (`br0`, `chZ`, `RCh`) 把第一分支, 孩子层的零, 孩子层的序交给 `T`.

```agda
mutual
  data L : Set where
    zero : L
    suc  : L → L
    lim  : (ℕ → L) → L
    Ωₗ   : (k : L) → (Tr k → L) → L

  Pos : L → Set
  Pos zero     = ⊥
  Pos (suc a)  = Pos⁼ a
  Pos (lim g)  = Σ ℕ λ n → Pos⁼ (g n)
  Pos (Ωₗ k h) = Pos⁼ k ⊎ Σ (Tr k) λ c → Pos⁼ (h c)

  Pos⁼ : L → Set
  Pos⁼ a = ⊤ ⊎ Pos a

  Br : (ℓ : L) → Pos ℓ → Set
  Br (suc a)  t              = Br⁼ a t
  Br (lim g)  (n , t)        = Br⁼ (g n) t
  Br (Ωₗ k h) (inj₁ t)       = Br⁼ k t
  Br (Ωₗ k h) (inj₂ (c , t)) = Br⁼ (h c) t

  Br⁼ : (a : L) → Pos⁼ a → Set
  Br⁼ a (inj₁ _) = Tr a
  Br⁼ a (inj₂ p) = Br a p

  Ch : L → Set
  Ch zero     = ⊥
  Ch (suc a)  = ⊤
  Ch (lim g)  = ℕ
  Ch (Ωₗ k h) = Tr k

  ChT : (ℓ : L) → Ch ℓ → Set
  ChT (suc a)  _ = Tr a
  ChT (lim g)  n = Tr (g n)
  ChT (Ωₗ k h) c = Tr (h c)

  Sig : L → Sg
  Sig ℓ = sg (Pos ℓ) (Br ℓ) (Ch ℓ) (ChT ℓ) (br0 ℓ) (chZ ℓ) (RCh ℓ)

  Tr : L → Set
  Tr ℓ = T (Sig ℓ)

  br0 : (ℓ : L) (p : Pos ℓ) → Br ℓ p
  br0 (suc a)  t              = br0⁼ a t
  br0 (lim g)  (n , t)        = br0⁼ (g n) t
  br0 (Ωₗ k h) (inj₁ t)       = br0⁼ k t
  br0 (Ωₗ k h) (inj₂ (c , t)) = br0⁼ (h c) t

  br0⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t
  br0⁼ a (inj₁ _) = zero
  br0⁼ a (inj₂ p) = br0 a p

  chZ : (ℓ : L) (c : Ch ℓ) → ChT ℓ c
  chZ (suc a)  _ = zero
  chZ (lim g)  n = zero
  chZ (Ωₗ k h) c = zero

  RCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → ChT ℓ c → Set
  RCh (suc a)  _ = Lt (Sig a)
  RCh (lim g)  n = Lt (Sig (g n))
  RCh (Ωₗ k h) c = Lt (Sig (h c))

infix 4 _⊢_◃_
_⊢_◃_ : (ℓ : L) → Tr ℓ → Tr ℓ → Set
ℓ ⊢ x ◃ y = Lt (Sig ℓ) x y
```

槽位所在的层号, 该层的树到分支类型的换型 (每一情形都是恒等), 第一分支就是零.

```agda
mutual
  at : (ℓ : L) → Pos ℓ → L
  at (suc a)  t              = at⁼ a t
  at (lim g)  (n , t)        = at⁼ (g n) t
  at (Ωₗ k h) (inj₁ t)       = at⁼ k t
  at (Ωₗ k h) (inj₂ (c , t)) = at⁼ (h c) t

  at⁼ : (a : L) → Pos⁼ a → L
  at⁼ a (inj₁ _) = a
  at⁼ a (inj₂ p) = at a p

mutual
  fromBr : (ℓ : L) (p : Pos ℓ) → Tr (at ℓ p) → Br ℓ p
  fromBr (suc a)  t              x = fromBr⁼ a t x
  fromBr (lim g)  (n , t)        x = fromBr⁼ (g n) t x
  fromBr (Ωₗ k h) (inj₁ t)       x = fromBr⁼ k t x
  fromBr (Ωₗ k h) (inj₂ (c , t)) x = fromBr⁼ (h c) t x

  fromBr⁼ : (a : L) (t : Pos⁼ a) → Tr (at⁼ a t) → Br⁼ a t
  fromBr⁼ a (inj₁ _) x = x
  fromBr⁼ a (inj₂ p) x = fromBr a p x

mutual
  br0≡ : (ℓ : L) (p : Pos ℓ) → br0 ℓ p ≡ fromBr ℓ p zero
  br0≡ (suc a)  t              = br0⁼≡ a t
  br0≡ (lim g)  (n , t)        = br0⁼≡ (g n) t
  br0≡ (Ωₗ k h) (inj₁ t)       = br0⁼≡ k t
  br0≡ (Ωₗ k h) (inj₂ (c , t)) = br0⁼≡ (h c) t

  br0⁼≡ : (a : L) (t : Pos⁼ a) → br0⁼ a t ≡ fromBr⁼ a t zero
  br0⁼≡ a (inj₁ _) = refl
  br0⁼≡ a (inj₂ p) = br0≡ a p

chL : (ℓ : L) → Ch ℓ → L
chL (suc a)  _ = a
chL (lim g)  n = g n
chL (Ωₗ k h) c = h c
```

## 读回, 塔, Λ

树读成层号 (`↑`); `up x c y e` 读成 ↑x ⊕ ↑y. 塔的分支 c 现在只取合法树.

```agda
infixl 6 _⊕_
_⊕_ : L → L → L
a ⊕ zero     = a
a ⊕ suc b    = suc (a ⊕ b)
a ⊕ lim g    = lim (λ n → a ⊕ g n)
a ⊕ Ωₗ k h   = Ωₗ k (λ c → a ⊕ h c)

mutual
  ↑ : (k : L) → Tr k → L
  ↑ k zero         = zero
  ↑ k (suc x)      = suc (↑ k x)
  ↑ k (lim f _)    = lim (λ n → ↑ k (f n))
  ↑ k (Ω p g)      = Ωₗ (at k p) (λ c → ↑ k (g (fromBr k p c)))
  ↑ k (up x c y _) = ↑ k x ⊕ ↑ch k c y

  ↑ch : (k : L) (c : Ch k) → ChT k c → L
  ↑ch (suc a)  _ y = ↑ a y
  ↑ch (lim g)  n y = ↑ (g n) y
  ↑ch (Ωₗ k h) c y = ↑ (h c) y

tw : ℕ → L
tw zero    = zero
tw (suc n) = Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)

Λ : L
Λ = lim tw
```
