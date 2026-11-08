# 实际中Ω的完整部分和覆盖接口

中槽从原floor0启动；底槽u显式保留。原middle回灌更新中槽，输出
调用low u b，而不是terminal与mid复合。覆盖目标是原normal1的末段输出。
这里只比较Cd值，不作高度下标比较；源/目标层号均为固定有限层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueCoverIf where
open import Data.Nat using (ℕ; zero)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedWorldValueTwoSlot
import OCF.Lean.Fold1Fold as F
import OCF.Align.BoundedCompletionOutputCoverIf as Target
import OCF.Align.BoundedNativeValueFirst as V

module Middle (u : Cd) = F.Col _⊞_ _⊞_ (floor zero) (floor zero) (λ _ e → e)
  (λ b e → mid b (up e)) (λ b e → low u b (up e))

record MiddleCover : Set where
  field
    sums : ∀ u → u ≤ᵛ V.feedback → ∀ n → Middle.oO u n ≤ᵛ Target.output
```

这是一整个中Ω的所有输出部分和；不是其坐标条件。它足以覆盖low u floor0
floor1，但尚未包含Old3后续的中Ω分支prefix⊞up e。
