# 旧第二地板整输出的实际覆盖接口

目标固定为原Θ.normal1经原末段的完整输出；它不是Sample.normalized1
（后者使用normal2）。从本目标进入第二真实采样需另接实际选择桥。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputCoverIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value)
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Lean.Fold1 as F
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import Data.Unit using (tt)

output : Cd
output = T.fold V.feedback (Θ.normal 1)

record Coverage : Set where
  field
    sums : ∀ n → Old.Pure.oO n ≤ᵛ output

finish : Coverage → F.TΩ (num 2) tt ≤ᵛ output
finish c = ≤-trans (same-value Old.old2) (l≤ (Coverage.sums c))
```

接口要求全部旧输出部分和覆盖，不以仅坐标序或有限测试替代。
