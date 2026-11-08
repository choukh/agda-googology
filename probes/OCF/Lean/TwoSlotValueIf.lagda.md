# 原双低槽解释器的联合有向比较

中槽仍是原生第零层树，底槽仍是可数树；两者分别带分层Value与
可数值序。输入关系保留旧Ω和中Ω的不同坐标关系，不把高层裸值序
送过折叠。本接口只量化固定源层2内的树，不要求裸下标比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TwoSlotValueIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldValueTwoSlot using (mid; low)

record JointComparison : Set₁ where
  field
    middle : ∀ {a b u v} → Value (num 1) a b → Value hz u v →
      Value hz (mid u a) (mid v b)
    lower : ∀ {a b u v x y} → Value (num 1) a b → Value hz u v → x ≤ᵛ y →
      low x u a ≤ᵛ low y v b
```

接口没有假设全部raw树自相关。后续给实际地板与原Old3全部坐标的
自证实例；比较的双方中槽与底槽可以同时不同。
