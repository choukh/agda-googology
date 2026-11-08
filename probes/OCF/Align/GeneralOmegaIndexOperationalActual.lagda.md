# 原完整ΛL输出的完成保值

阶段逐字取run ΛL (ΣF twL n)。原ι与ΣF累计前缀由运行上下文直接
实例化，不改成put，不替换闭项。塔根只有三种形状足以覆盖全部n。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexOperationalActual where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; ΛL; twL)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Align.GeneralOmegaIndexRaise
open import OCF.Align.GeneralOmegaIndexOperationalIf
import OCF.Align.GeneralOmegaIndexOperationalRun as R
import OCF.Lean.GeneralOmegaCompletionSeries as Series
import OCF.Lean.GeneralOmegaConsumeClosed as Closed

data Root : LH → Set where
  zero : Root lz
  one : Root (ls lz)
  index : ∀ g → Root (lΩ lz g)
Ω-root : ∀ {x} → Root x → Root (ΩL x)
Ω-root zero = one
Ω-root one = index _
Ω-root (index g) = index _
tower-root : ∀ n → Root (twL n)
tower-root zero = zero
tower-root (suc n) = Ω-root (tower-root n)

root-stable : ∀ x → Root x → ∀ y (j : Context (ΩL x) y) →
  leg (run y (read j (flL (ΩL x)))) ≤ᵛ run y (read j (flL (ΩL x)))
root-stable .lz zero y j = R.Next.stable lz y j
root-stable .(ls lz) one y j = R.Successor.stable lz y j
root-stable .(lΩ lz g) (index g) y j = R.Index.stable lz g y j

stage : ℕ → Cd
stage n = run ΛL (ΣF twL n)
context : ∀ n → Context (twL (suc n)) ΛL
context n = compose (prefix ΛL (ΣF twL n)) (sum twL (suc n))
stable : ∀ n → leg (stage n) ≤ᵛ stage n
stable zero = ≤-refl _
stable (suc n) = root-stable (twL n) (tower-root n) ΛL (context n)
growth : ∀ n → Ops.repeat S⊥ (stage n) ≤ᵛ stage (suc n)
growth n = R.Mapped.repeated (identity ΛL) (ΣF twL n)
  (raises-ι (suc n) (floor-raises (Ω-shape (twL n))))
stages : Series.Stages stage
stages = record { stable = stable ; growth = growth }

completed≤raw : Closed.tree ≤ᵛ Closed.raw
completed≤raw = Series.Result.upper stage stages
raw≤completed : Closed.raw ≤ᵛ Closed.tree
raw≤completed = Closed.raw-lower
```

已比较完整原ΛL地板的所有阶段与最终外层leg，故完成没有提高此闭项
的序数值。此上界是“完成树≤原raw”，不是具名序数上界；它不说明
raw已达到EBO，也不推出FGH相等。此前Old.TΩ1下界仍成立。
