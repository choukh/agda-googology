# 中Ω完整输出和的底槽参数覆盖

底槽不是固定零，而是任何被实际反馈值控制的u。u=0的值界已知，本篇
不把它重新报告成强度进展；用途是给两槽模型一个真正可满足的输出契约。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueCoverRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionTerminalValueAct using (old-coordinate-self)
open import OCF.Align.BoundedCompletionOutputPadding using (pad; pad-self; padded-add)
open import OCF.Align.BoundedCompletionOutputCoverStride using (stride; padded-partial)
open import OCF.Align.BoundedWorldValueCoverIf
import OCF.Align.BoundedWorldValueCoverReduce as R
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedCompletionOutputCoverModel as M
import OCF.Align.BoundedCompletionOutputCoverIf as Target
import OCF.Align.BoundedCompletionOutputAcceptLift as Lift
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeCompletionClosed as C
open import OCF.Align.BoundedWorldValueTwoSlot using (low)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)

partial-pad : ∀ u n → Middle.oO u n ≤ᵛ T.fold u (pad Old.Pure.ce n)
partial-pad u zero = same-value (R.outputs u zero)
partial-pad u (suc n) = ≤-trans
  (add-mono (partial-pad u n) (same-value (R.outputs u (suc n))))
  (padded-add (pad-self Old.Pure.ce old-coordinate-self n)
    (old-coordinate-self (suc n)) (≤-refl u) (≤-refl u))

sums : ∀ u → u ≤ᵛ V.feedback → ∀ n → Middle.oO u n ≤ᵛ Target.output
sums u bound n = ≤-trans (partial-pad u n)
  (≤-trans (eval (padded-partial n) bound)
    (≤-trans (≤l (stride n) (≤-refl _))
      (same-value (same-sym M.actual-output))))

instance-cover : MiddleCover
instance-cover = record { sums = sums }

whole : ∀ u → u ≤ᵛ V.feedback → low u (floor zero) (floor 1) ≤ᵛ Target.output
whole u bound = l≤ (sums u bound)
whole≤C : ∀ u → u ≤ᵛ V.feedback → low u (floor zero) (floor 1) ≤ᵛ C.tree
whole≤C u bound = ≤-trans (whole u bound) Lift.whole≤C

-- 非零实际底槽实例；不是用矛盾前提闭接口。
actual-feedback : low V.feedback (floor zero) (floor 1) ≤ᵛ C.tree
actual-feedback = whole≤C V.feedback (≤-refl V.feedback)
```

尚不能把whole用到Old3第1输出：其输入含floor1前缀，进入中Ω分支后
该前缀本身仍会读取/更新中槽，故low-up的消槽前提不成立。这个确切区别
是下一需要处理的字段，不是路线否定。
