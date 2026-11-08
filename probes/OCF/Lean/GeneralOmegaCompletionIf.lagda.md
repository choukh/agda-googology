# 原反馈链捕获其完成坐标时的值接口

完成一般会增值。本接口要求每个实际链点的完成值已由该点的回调
输出覆盖；只量化原chain，不要求全部raw回调或函数值同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCompletionIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)

record Capture (H : Cd → Cd) : Set where
  field
    on-chain : ∀ n → leg (chain H n) ≤ᵛ H (chain H n)

record Stable (H : Cd → Cd) : Set where
  field
    upper : leg (diagonal H H) ≤ᵛ diagonal H H
```

Capture是充分条件，不宣称必要。后续先对强逐形覆盖证明原输出和被
下一坐标捕获，再用此字段；不会把一般raw值比较穿过leg。
