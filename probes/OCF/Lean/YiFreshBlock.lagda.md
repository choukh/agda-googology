# 空白页样本: 块

> 判决: 成品候选 (块). 层号 `L` 与各层的树 `Tr` 归纳-递归地一起定义; 层号含零, 后继, ℕ 极限, 以低层树为分支的 Ω 结点 `Ωₗ`.
> 树的 Ω 结点的槽位是层号里的路径 `Pos`, 不是比较出来的下标; 孩子层的树以 `up` 原样嵌入, 不摊开.
> 不否定什么. 折叠在 `YiFreshFold`, 合法性在 `YiFreshLegal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
```

一层的树. 参数: 槽位 `P`, 槽位上的分支类型 `B`, 孩子 `C` 与孩子层的树 `D`.
`up x c y` 读作 x + ↑y, 其中 y 是孩子 c 那一层的树, 原样保留.

```agda
data T (P : Set) (B : P → Set) (C : Set) (D : C → Set) : Set where
  zero : T P B C D
  suc  : T P B C D → T P B C D
  lim  : (ℕ → T P B C D) → T P B C D
  Ω    : (p : P) → (B p → T P B C D) → T P B C D
  up   : T P B C D → (c : C) → D c → T P B C D
```

`Pos ℓ` 是严格低于 ℓ 的槽位, `Pos⁼ a` 再加上 a 自身 (`inj₁ tt`).
`Ωₗ k h` 的槽位分两侧: 经 k (`inj₁`), 或经分支 c 进入 h c (`inj₂`). 分支类型 `Br` 与槽位同步递归, 使 `Tr` 的递归结构化.

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

  Tr : L → Set
  Tr ℓ = T (Pos ℓ) (Br ℓ) (Ch ℓ) (ChT ℓ)
```

槽位所在的层号, 以及分支类型与该层树的互换 (每一情形都是恒等).

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
  toBr : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Tr (at ℓ p)
  toBr (suc a)  t              x = toBr⁼ a t x
  toBr (lim g)  (n , t)        x = toBr⁼ (g n) t x
  toBr (Ωₗ k h) (inj₁ t)       x = toBr⁼ k t x
  toBr (Ωₗ k h) (inj₂ (c , t)) x = toBr⁼ (h c) t x

  toBr⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Tr (at⁼ a t)
  toBr⁼ a (inj₁ _) x = x
  toBr⁼ a (inj₂ p) x = toBr a p x
```

树读成层号 (`↑`), 用于塔. `up x c y` 读成 ↑x ⊕ ↑y.

```agda
infixl 6 _⊕_
_⊕_ : L → L → L
a ⊕ zero     = a
a ⊕ suc b    = suc (a ⊕ b)
a ⊕ lim g    = lim (λ n → a ⊕ g n)
a ⊕ Ωₗ k h   = Ωₗ k (λ c → a ⊕ h c)

mutual
  ↑ : (k : L) → Tr k → L
  ↑ k zero       = zero
  ↑ k (suc x)    = suc (↑ k x)
  ↑ k (lim f)    = lim (λ n → ↑ k (f n))
  ↑ k (Ω p g)    = Ωₗ (at k p) (λ c → ↑ k (g (fromBr k p c)))
  ↑ k (up x c y) = ↑ k x ⊕ ↑ch k c y

  ↑ch : (k : L) (c : Ch k) → ChT k c → L
  ↑ch (suc a)  _ y = ↑ a y
  ↑ch (lim g)  n y = ↑ (g n) y
  ↑ch (Ωₗ k h) c y = ↑ (h c) y
```

孩子的层号与孩子树的换型 (恒等).

```agda
chL : (ℓ : L) → Ch ℓ → L
chL (suc a)  _ = a
chL (lim g)  n = g n
chL (Ωₗ k h) c = h c

chT : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Tr (chL ℓ c)
chT (suc a)  _ y = y
chT (lim g)  n y = y
chT (Ωₗ k h) c y = y
```

塔与它的极限 (J1). 分支层号写成 tw n ⊕ ↑c, 使第一分支 (c = 0) 恰是 tw n; 上确界不变.

```agda
tw : ℕ → L
tw zero    = zero
tw (suc n) = Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)

Λ : L
Λ = lim tw
```
