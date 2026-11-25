# 合法性进块: 合法性作 Σ 的写法 (对照)

> 判决: 对照用的块, 不是主候选. 检查器接受: 树 `T` 不带证明, 合法性 `Leg` 与第一位置序进入归纳-递归的结, `LTr a = Σ (Tr a) (Leg a)`; `Ωₗ k h` 的 `h`, 分支 `Br`, 孩子下标 `Ch` 都取 `LTr`.
> 这个写法上没有做折叠 (未走通, 没有编译的否定). 判断: 链步回灌要 "折叠输出合法", 折叠须带着合法性证明走, 单调性就要对同一棵树的两份独立证明陈述, `◃t` 的中间点没有证明可用.
> 不否定什么. 主候选把相邻步进与非零放进树的构造子 (`YiLegBlock`), 那里上述两处不出现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegBlockSigma where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

## 一层的树, 序, 合法性 (对参数泛化, 在结之外)

```agda
data T (P : Set) (B : P → Set) (C : Set) (D : C → Set) : Set where
  zero : T P B C D
  suc  : T P B C D → T P B C D
  lim  : (ℕ → T P B C D) → T P B C D
  Ω    : (p : P) → (B p → T P B C D) → T P B C D
  up   : T P B C D → (c : C) → D c → T P B C D

module G {P : Set} {B : P → Set} {C : Set} {D : C → Set}
  (b₀ : (p : P) → B p) (z₀ : (c : C) → D c) (R : (c : C) → D c → D c → Set) (LC : (c : C) → D c → Set) where
  data Lt : T P B C D → T P B C D → Set where
    ◃s : ∀ {x} → Lt x (suc x)
    ◃l : ∀ {f} (n : ℕ) → Lt (f n) (lim f)
    ◃w : ∀ {p g} → Lt (g (b₀ p)) (Ω p g)
    ◃u : ∀ {x c y} → R c (z₀ c) y → Lt x (up x c y)
    ◃c : ∀ {x c y′ y} → R c y′ y → Lt (up x c y′) (up x c y)
    ◃t : ∀ {x y z} → Lt x y → Lt y z → Lt x z
  LegT : T P B C D → Set
  LegT zero       = ⊤
  LegT (suc x)    = LegT x
  LegT (lim f)    = ((n : ℕ) → LegT (f n)) × ((n : ℕ) → Lt (f n) (f (suc n)))
  LegT (Ω p g)    = (z : B p) → LegT (g z)
  LegT (up x c y) = LegT x × LC c y × R c (z₀ c) y
```

## 层号, 各层的树, 合法性 (一个结)

`Leg` 的子句写在 `br0⁼` 之前, 使 `zero , tt` 的第二分量的类型能化简成 `⊤`.

```agda
mutual
  data L : Set where
    zero : L
    suc  : L → L
    lim  : (ℕ → L) → L
    Ωₗ   : (k : L) → (LTr k → L) → L

  Pos : L → Set
  Pos zero     = ⊥
  Pos (suc a)  = Pos⁼ a
  Pos (lim g)  = Σ ℕ λ n → Pos⁼ (g n)
  Pos (Ωₗ k h) = Pos⁼ k ⊎ Σ (LTr k) λ c → Pos⁼ (h c)

  Pos⁼ : L → Set
  Pos⁼ a = ⊤ ⊎ Pos a

  Br : (ℓ : L) → Pos ℓ → Set
  Br (suc a)  t              = Br⁼ a t
  Br (lim g)  (n , t)        = Br⁼ (g n) t
  Br (Ωₗ k h) (inj₁ t)       = Br⁼ k t
  Br (Ωₗ k h) (inj₂ (c , t)) = Br⁼ (h c) t

  Br⁼ : (a : L) → Pos⁼ a → Set
  Br⁼ a (inj₁ _) = LTr a
  Br⁼ a (inj₂ p) = Br a p

  Ch : L → Set
  Ch zero     = ⊥
  Ch (suc a)  = ⊤
  Ch (lim g)  = ℕ
  Ch (Ωₗ k h) = LTr k

  ChT : (ℓ : L) → Ch ℓ → Set
  ChT (suc a)  _ = Tr a
  ChT (lim g)  n = Tr (g n)
  ChT (Ωₗ k h) c = Tr (h c)

  Tr : L → Set
  Tr ℓ = T (Pos ℓ) (Br ℓ) (Ch ℓ) (ChT ℓ)

  Leg : (ℓ : L) → Tr ℓ → Set
  Leg ℓ = G.LegT (br0 ℓ) (chZ ℓ) (RCh ℓ) (LegCh ℓ)

  LTr : L → Set
  LTr ℓ = Σ (Tr ℓ) (Leg ℓ)

  br0 : (ℓ : L) (p : Pos ℓ) → Br ℓ p
  br0 (suc a)  t              = br0⁼ a t
  br0 (lim g)  (n , t)        = br0⁼ (g n) t
  br0 (Ωₗ k h) (inj₁ t)       = br0⁼ k t
  br0 (Ωₗ k h) (inj₂ (c , t)) = br0⁼ (h c) t

  br0⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t
  br0⁼ a (inj₁ _) = zero , tt
  br0⁼ a (inj₂ p) = br0 a p

  chZ : (ℓ : L) (c : Ch ℓ) → ChT ℓ c
  chZ (suc a)  _ = zero
  chZ (lim g)  n = zero
  chZ (Ωₗ k h) c = zero

  RCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → ChT ℓ c → Set
  RCh (suc a)  _ = Lt′ a
  RCh (lim g)  n = Lt′ (g n)
  RCh (Ωₗ k h) c = Lt′ (h c)

  Lt′ : (ℓ : L) → Tr ℓ → Tr ℓ → Set
  Lt′ ℓ = G.Lt (br0 ℓ) (chZ ℓ) (RCh ℓ) (LegCh ℓ)

  LegCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  LegCh (suc a)  _ = Leg a
  LegCh (lim g)  n = Leg (g n)
  LegCh (Ωₗ k h) c = Leg (h c)
```
