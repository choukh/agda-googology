# 多种类世界索引树：保留节点的接口

接口定稿 2026-11-06。依据 `WorldObstructionValue`，路径稳定性不足以
保证升世界保值。因此这里不把升世界的值不变加入接口；先把需要的数据
分开。旧 `W` 固定可数坐标，本接口允许每个种类自己的坐标类型。

节点的分支量化所有未来世界：在当前世界 `w` 建节点，就须能在任意
`v ≥ w`、任意该世界内可入坐标处分支。升世界只限制这个量化范围，
不反向搬运坐标。这个设计选择是否足够写 Λ 层折叠，仍是开放义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerWorldIf where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_)

record Signature : Set₁ where
  field
    World : Set
    _≤w_ : World → World → Set
    reflw : ∀ w → w ≤w w
    transw : ∀ {u v w} → u ≤w v → v ≤w w → u ≤w w
    Kind : Set
    Coord : Kind → Set
    LegalCoord : ∀ k → Coord k → Set
    Admit : (w : World) → ∀ k → Coord k → Set
    admitted-legal : ∀ {w k c} → Admit w k c → LegalCoord k c
    next : (w : World) → ∀ k (c : Coord k) → Admit w k c → World

module Trees (S : Signature) where
  open Signature S
  data Tree (w : World) : Set where
    zero : Tree w
    suc : Tree w → Tree w
    lim : (ℕ → Tree w) → Tree w
    node : (k : Kind) →
      ((v : World) → w ≤w v → (c : Coord k) → (a : Admit v k c) → Tree (next v k c a)) → Tree w

  -- 同种类的世界上移不要求 Coord 的反向映射。
  lift : ∀ {u v} → u ≤w v → Tree u → Tree v
  lift p zero = zero
  lift p (suc t) = suc (lift p t)
  lift p (lim f) = lim (λ n → lift p (f n))
  lift p (node k g) = node k (λ v q c a → g v (transw p q) c a)

  -- 跨种类/跨签名的保留节点则不同：其坐标方向必须明确。
record Keep (S T : Signature) : Set₁ where
  field
    world : Signature.World S → Signature.World T
    kind : Signature.Kind S → Signature.Kind T
    -- 这里不假装世界索引会自动提供这个反变函数。
    coordinate : ∀ k → Signature.Coord T (kind k) → Signature.Coord S k
    legal-coordinate : ∀ k c → Signature.LegalCoord T (kind k) c → Signature.LegalCoord S k (coordinate k c)
```

`Keep` 只记录跨种类所需数据，尚不是完整折叠规格；没有给可入搬运律、
分支目标世界相干律或回灌闭包。没有任何裸下标比较律。
内部 View 必须同时给语义与递归性；本文件只有显式递归树构造子，
不把跨世界子树自动当成已满足作者要求的同类型语义 View。

## 前缀进入分支所需的一条世界律

```agda
record NextUp (S : Signature) : Set₁ where
  open Signature S
  field
    up : ∀ w k c (a : Admit w k c) → w ≤w next w k c a
```
