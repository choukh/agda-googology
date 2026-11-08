# κ₀ 后继分支的实际 κ₁ 首格

本篇只取原运行器的一次真实反馈，不改运行规则或状态。
κ₀ 的内部枝为 `n1`，所以它会执行原 `Stp` 动作，不能以零枝消去。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnValueStep where

open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
import OCF.Align.EvFoldClosed as Closed
import OCF.Align.EventReturnValueCell as Base
open Base.R

branch : Bu Closed.three Closed.W₁
branch q l = nε κ₀ tt (λ _ _ → n1)

cell : Clε Closed.W₁ Closed.W₁ Closed.three
cell = κcε accᴸ κ₁ branch ≤rf (tt , tt) hself Act n0 Base.state zero

output : D₂ (Closed.one , hc cell)
output = yc (κΔε accᴸ branch ≤rf (tt , tt) hself Act cell) (τ₂ (tt , tt))

```

尝试 `∀ b → rd₂ (tt , tt) b output ≡ rd₂ {Closed.W₁} (tt , tt) b
(drp₂ output)` 用 `refl`：6G 编译退出 42，未能把旧事件表
`evRB κ₁ … ∷ []` 与 `[]` 统一。这不是该等式或值覆盖的否定。
本篇仅保存实际输出定义，不导出上述未证结论。
