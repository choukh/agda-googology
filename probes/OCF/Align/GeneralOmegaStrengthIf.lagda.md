# 原阶段的完整纯反馈闭包增长

值验收专用。Close保留原diagonal的seed1和全部累加坐标，但不调用leg。
这里的迭代是待证下界参照，不替换原Λ闭项或它的stage。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaStrengthIf where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Align.FrozenAbsorbNegUpper using (P)
open import OCF.Align.GeneralOmegaIndexOperationalActual using (stage)

Close : Cd → Cd
Close a = diagonal (P a) (P a)
iterate : ℕ → Cd
iterate zero = hs hz
iterate (suc n) = Close (iterate n)
reference : Cd
reference = hl iterate

record Strength : Set where
  field
    stage-close : ∀ n → Close (stage n) ≤ᵛ stage (suc n)
    iteration : ∀ n → iterate n ≤ᵛ stage n
```

前提无悬空参数：原stage已经是固定run ΛL ΣF twL。StageCore的EBO
第二站族另含ψ⁰(Ω(toLevel γn))；本Close迭代不自动等于该记号族。
