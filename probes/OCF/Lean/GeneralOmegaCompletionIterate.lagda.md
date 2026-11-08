# 外层完成判据的实际闭包迭代实例

用已经有真实原后继层解释的closure生成族填Stages，确保外层条件
可满足。这一族只是判据实例，不偷换原ΛL的累计分量族。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCompletionIterate where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaConsumeLayerIf using (closure)
open import OCF.Lean.GeneralOmegaCompletionActual using (closure-upper)
open import OCF.Lean.TowerCollapseIf using (module Ops)
import OCF.Lean.GeneralOmegaCompletionSeries as Series

family : ℕ → Cd
family zero = closure (hs hz)
family (suc n) = closure (family n)
positive : ∀ n → hs hz ≤ᵛ family n
positive zero = ≤l 0 (≤l 0 (≤-refl _))
positive (suc n) = ≤l 0 (≤l 0 (positive n))
stable : ∀ n → leg (family n) ≤ᵛ family n
stable zero = closure-upper (hs hz) (≤-refl _)
stable (suc n) = closure-upper (family n) (positive n)
growth : ∀ n → Ops.repeat S⊥ (family n) ≤ᵛ family (suc n)
growth n = ≤l 0 (≤-refl _)
actual-stages : Series.Stages family
actual-stages = record { stable = stable; growth = growth }
upper : leg (hl family) ≤ᵛ hl family
upper = Series.Result.upper family actual-stages
lower : hl family ≤ᵛ leg (hl family)
lower = inflation (hl family)
```

实例没有标签、没有全raw合法性或全局比较前提。这里的upper/lower
仅属于这个明确族；原完整Λ源仍须单独证明它自己的Stages字段。
