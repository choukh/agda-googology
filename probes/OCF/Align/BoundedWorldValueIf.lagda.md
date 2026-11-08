# 带完整世界的两轨道有向模拟

本接口直接用原 Col；更新作用于初始世界，输出部分和也不换定义。
世界关系与坐标、输出关系分开，不从有向关系推出端点自相关。
它不比较层号；实际折叠实例的层号公共界在实例文件给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueIf where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
import OCF.Lean.Fold1Fold as F

record Simulation {A B : Set} {S T : KS}
  (WR : A → B → Set) (XR : HB S → HB S → Set) (TR : HB T → HB T → Set)
  (wa : A) (wb : B) (a b : HB S)
  (ua : A → HB S → A) (ub : B → HB S → B)
  (fx : A → HB S → HB S) (gx : B → HB S → HB S)
  (ft : A → HB S → HB T) (gt : B → HB S → HB T) : Set where
  field
    worlds-start : WR wa wb
    coordinates-start : XR a b
    add-coordinate : ∀ {a b c d} → XR a b → XR c d → XR (a ⊞ c) (b ⊞ d)
    add-output : ∀ {a b c d} → TR a b → TR c d → TR (a ⊞ c) (b ⊞ d)
    update : ∀ {w v x y} → WR w v → XR x y → WR (ua w x) (ub v y)
    advance : ∀ {w v x y} → WR w v → XR x y → XR (fx w x) (gx v y)
    emit : ∀ {w v x y} → WR w v → XR x y → TR (ft w x) (gt v y)

  module Left = F.Col _⊞_ _⊞_ wa a ua fx ft
  module Right = F.Col _⊞_ _⊞_ wb b ub gx gt
```

fields中的step与emit是单次子树模拟，不是假定整个闭项的输出覆盖。
实例将同时保留底槽与中槽，并用同一接口累计完整输出和。
