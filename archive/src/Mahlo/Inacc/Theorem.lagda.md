# 主定理（无条件版本）

用 [FactsImpl](FactsImpl.lagda.md) 构造的 `facts` 实例化 [WO.Main](WO/Main.lagda.md) 与 [FGH](FGH.lagda.md)：
Theorem 4.41 与其推论（每个 `y ≺ ψ_{Ω₁}(Ω′_{I+n})`，`y ∈ OT`，都是良基的）以及大数 `𝔑`，不再带任何假设。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Theorem where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.FactsImpl

open import Data.Nat.Base using (ℕ)

import Mahlo.Inacc.WO.Main facts as Main
import Mahlo.Inacc.FGH facts as FGH

open Main public using (endpt; Acc; Acc-endpt; thm441)
open FGH  public using (F′; Fₙ; BIG; 𝔑)

-- 每个 OT 项 y ≺ ψ_{Ω₁}(Ω′_{I+n}) 可达（Theorem 4.41 的实例化）
wellfounded : ∀ n {y} → OT y → y ≺ endpt n → Acc y
wellfounded = Acc-endpt

-- 大数：ℕ 中的一个闭项，由 F_{ψ_{Ω₁}(Ω′_{I+8})}(8) 给出
𝔑′ : ℕ
𝔑′ = 𝔑
```
