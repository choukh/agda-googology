# 阶段无关延迟定理的真实旧第二地板实例

这里不是只给关系的恒等玩具：old直接取Old.Pure全轨道，padded直接
取原补偿族，结论仍把完整旧第二地板放入原合法C。没有改写旧特例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedStrideActual where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Lean.BoundedStrideIf
import OCF.Lean.BoundedStrideRun as Generic
open import OCF.Align.BoundedCompletionTerminalValueIf using (U; VRel)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (prefix-rel; add-rel)
import OCF.Align.BoundedCompletionOutputPadding as P
import OCF.Align.BoundedCompletionOutputCoverStride as Previous
import OCF.Align.BoundedCompletionOutputCoverModel as M
import OCF.Align.BoundedCompletionOutputAcceptLift as Lift
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Lean.Fold1 as F
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)

actual-laws : StrideLaws U VRel Old.act M.H Old.Pure.ce (P.pad Old.Pure.ce)
actual-laws = record
  { old-step = λ n → refl
  ; pad-zero = refl
  ; pad-step = λ n → refl
  ; append = prefix-rel
  ; prepend = P.right-rel
  ; add = add-rel
  ; inflate = Previous.step-inflate
  ; action = Previous.step-act
  ; positive = Previous.step-positive
  ; initial = Previous.initial }

module Actual = Generic.Run actual-laws

actual-sums : ∀ n → Old.Pure.oO n ≤ᵛ M.output
actual-sums n = ≤-trans (P.old-padded-sums n)
  (≤-trans (eval (Actual.padded-partial n) z≤)
    (≤l (Generic.stride n) (≤-refl _)))

actual-old2≤C : F.TΩ (num 2) tt ≤ᵛ C.tree
actual-old2≤C = ≤-trans (same-value Old.old2)
  (≤-trans (l≤ actual-sums)
    (≤-trans (same-value (same-sym M.actual-output)) Lift.whole≤C))
```

新的一般定理确实消费同一实际模型及完整输出，前提可满足。它本身
不增加强度；作用是以后改变结构层参数时不重写三步延迟归纳。
