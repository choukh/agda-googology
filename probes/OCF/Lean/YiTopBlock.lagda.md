# 顶槽位的块: 块

> 判决: 成品候选 (块). 空白页的块 (`YiFreshBlock`) 去掉槽位路径: 没有 `Pos`, `Br`, `at`, `fromBr`, `toBr`; Ω 结点只在顶槽位, 分支是本层下标层的树.
> 有顶槽位的层号只有后继与 `Ωₗ` (`Hd`), 分支类型 `Bt` 是下标层的树; 层号, 孩子, 嵌入 `up`, 读回 `↑`, 塔与空白页相同.
> 不否定什么. 依据: `YiTopE2` (E2 的结点在顶槽位保留), `YiTopDom` (规范闭项与折叠都在顶槽位). 折叠在 `YiTopFold`, 合法性在 `YiTopLegal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
```

一层的树. `Ω s g`: s 是 "本层有顶槽位" 的证据, g 以下标层的树为分支.

```agda
data T (S : Set) (B : Set) (C : Set) (D : C → Set) : Set where
  zero : T S B C D
  suc  : T S B C D → T S B C D
  lim  : (ℕ → T S B C D) → T S B C D
  Ω    : S → (B → T S B C D) → T S B C D
  up   : T S B C D → (c : C) → D c → T S B C D

mutual
  data L : Set where
    zero : L
    suc  : L → L
    lim  : (ℕ → L) → L
    Ωₗ   : (k : L) → (Tr k → L) → L

  Hd : L → Set
  Hd (suc a)  = ⊤
  Hd (Ωₗ k h) = ⊤
  Hd _        = ⊥

  Bt : L → Set
  Bt (suc a)  = Tr a
  Bt (Ωₗ k h) = Tr k
  Bt _        = ⊤

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
  Tr ℓ = T (Hd ℓ) (Bt ℓ) (Ch ℓ) (ChT ℓ)
```

读回与塔 (同空白页; Ω 结点读回成以下标层为分支的 `Ωₗ`).

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
  ↑ (suc a)  (Ω _ g) = Ωₗ a (λ c → ↑ (suc a) (g c))
  ↑ (Ωₗ k h) (Ω _ g) = Ωₗ k (λ c → ↑ (Ωₗ k h) (g c))
  ↑ zero     (Ω () _)
  ↑ (lim _)  (Ω () _)
  ↑ k (up x c y) = ↑ k x ⊕ ↑ch k c y

  ↑ch : (k : L) (c : Ch k) → ChT k c → L
  ↑ch (suc a)  _ y = ↑ a y
  ↑ch (lim g)  n y = ↑ (g n) y
  ↑ch (Ωₗ k h) c y = ↑ (h c) y

chL : (ℓ : L) → Ch ℓ → L
chL (suc a)  _ = a
chL (lim g)  n = g n
chL (Ωₗ k h) c = h c

chT : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Tr (chL ℓ c)
chT (suc a)  _ y = y
chT (lim g)  n y = y
chT (Ωₗ k h) c y = y

tw : ℕ → L
tw zero    = zero
tw (suc n) = Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)

Λ : L
Λ = lim tw
```
