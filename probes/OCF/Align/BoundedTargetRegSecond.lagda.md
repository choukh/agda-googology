# 原全混合的第2部分和折叠合法

只引用原M的输入和fold；不改为合法化输出，也不通过副本Same猜测同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedTargetRegSecond where
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedTargetRegIf
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
import OCF.Lean.BoundedContextClosed as C
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Align.BoundedMixedFirstLegal as First
import OCF.Align.BoundedMixedSecondCoordinate as Coordinate
import OCF.Align.BoundedTargetRegClosure as Certificate
import OCF.Align.BoundedTargetRegAction as Output

module A = Output.Action (M.sums 1)

legal-at-two : LgB (M.Fold.fold hz (z⊲ᴮ C.B) (M.sums 2))
legal-at-two = LegalSum.sum-legal Base
  (λ n → A.run (chain Coordinate.Actual.run n))
  (λ n → A.legal First.legal-at-one _ (Certificate.actual-reg n)
    (Coordinate.actual-coordinate-legal n))
```

全部最高反馈坐标与每个输出点均由统一递归定理给证，不是有限取样。
不过本定理只完成n=2；OriginalPointwise的任意n仍待目标层索引证书推广。
