# 旧第二地板整输出进入原合法完成项

旧输出部分和先由一次后继补偿编码，再被三步延迟的新真实部分和覆盖。
最后使用已经证明的实际结构桥，不把坐标条件当作整输出结论。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputCoverRun where
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionOutputPadding using (old-padded-sums)
open import OCF.Align.BoundedCompletionOutputCoverIf
open import OCF.Align.BoundedCompletionOutputCoverStride using (stride; padded-partial)
import OCF.Align.BoundedCompletionOutputCoverModel as M
import OCF.Align.BoundedCompletionOutputAcceptLift as Lift
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedCompletionFinitePlaceSample as Actual
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Lean.Fold1 as F

sums : ∀ n → Old.Pure.oO n ≤ᵛ output
sums n = ≤-trans (old-padded-sums n)
  (≤-trans (eval (padded-partial n) z≤)
    (≤-trans (≤l (stride n) (OCF.Lean.Fold1Base.≤-refl _))
      (same-value (same-sym M.actual-output))))

instance-cover : Coverage
instance-cover = record { sums = sums }

old2≤normal1 : F.TΩ (num 2) tt ≤ᵛ output
old2≤normal1 = finish instance-cover

old2≤normalized1 : F.TΩ (num 2) tt ≤ᵛ Actual.normalized 1
old2≤normalized1 = ≤-trans old2≤normal1 Lift.whole≤normalized

old2≤C : F.TΩ (num 2) tt ≤ᵛ C.tree
old2≤C = ≤-trans old2≤normal1 Lift.whole≤C
```

old2≤C比较完整Old.TΩ2和原合法闭项C，无轨道覆盖假设。
Old.TΩ2的精确记号读法仍须独立验收；本篇没有把它直接命名为ψ₀(Ω₂)，
也没有证明全部有限塔或EBO参照都已被C覆盖。

翻译账：没有修改树、折叠或证书；pad只存在于证明，真实两条轨道均保留。
新用到的是树侧有向分支关系、加法的后继补偿和原前缀动作的统一膨胀。
