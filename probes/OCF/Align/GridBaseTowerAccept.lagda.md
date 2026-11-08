# 同一方格闭项的 ε₀ 基准下界

本篇仅验收，不进入闭项定义。借用已有纯幂塔与 ε₀ 参照树的
完整值校准；不将首站粗略读法当作 BTBO，也不称本结果为前沿提升。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GridBaseTowerAccept where

open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans)
import OCF.Lean.Fold1 as Old
import OCF.Align.GridBaseFirst as First
import OCF.Align.GridBaseTowerCore as Core
import OCF.Align.BoundedCompletionCalibrateTower as Tower
import OCF.Align.BoundedCompletionCalibrateAccept as Accept
import OCF.Lean.OutputDrivenGrid as Grid
import OCF.Lean.GridValueBase as Base

old-first-in-first : Old.TΩ1 ≤ᵛ First.first
old-first-in-first = ≤ᵛ-trans Tower.A≤E Core.tower-in-first

epsilon-in-first : Accept.epsilon ≤ᵛ First.first
epsilon-in-first = ≤ᵛ-trans Accept.epsilon≤A old-first-in-first

epsilon-in-grid : Accept.epsilon ≤ᵛ Grid.closedGrid
epsilon-in-grid = ≤ᵛ-trans epsilon-in-first Base.base-in-grid
```

这里的 `epsilon` 是已有通过记号验收的 ε₀ 参照。
结论只给下界；没有给 `closedGrid` 上界，也没有得到 ψ₀(Ω_Ω)
或 EBO 下界。完整高层回灌的值比较仍需单独完成。
