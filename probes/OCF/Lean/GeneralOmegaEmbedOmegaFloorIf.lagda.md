# 原地板关系的共享验收接口

本接口只记录原flL的结构闭包目标。lo′分量函数仍只接受原Layer中
明确给出的Tree坐标证据；不新增任意raw分支同余或值等价前提。
实例必须对全部Layer成立，因而可消费原twL与ΛL的既有Layer证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaFloorIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf

record FloorLaws : Set₁ where
  field
    add : ∀ {x y a b c d} (p : Layer x y) → Tree p a b → Tree p c d →
      Tree p (a ⊞ c) (b ⊞ d)
    floor : ∀ {x y} (p : Layer x y) → Tree p (flL x) (flL y)
```
