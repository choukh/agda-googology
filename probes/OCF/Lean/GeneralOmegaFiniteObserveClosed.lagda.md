# 包含全部有限源地板的无参数闭项

每个stage逐字观察原有限step塔的地板；没有用seed1的累计轨道替代
高节点自己的floor初界。外层leg提供合法可数树，值验收另行对原
stage展开，不能从层数直接命名其序数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteObserveClosed where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Lean.Fold1 as FGH

zero-path : ∀ n → Within n zero
zero-path zero = here
zero-path (suc n) = lower (zero-path n)
stage : ℕ → Cd
stage n = observe (zero-path n) (floor n)
raw : Cd
raw = hl stage
tree : Cd
tree = leg raw
legal : LgB tree
legal = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw
stage-lower : ∀ n → stage n ≤ᵛ tree
stage-lower n = ≤-trans (≤l n (≤-refl _)) raw-lower
fgh : ℕ → ℕ
fgh = FGH.FGH tree
```

已交合法闭项及全部真实stage进入闭项的值定理。原typed有限族到
stage的完整桥、leg是否保此新闭项的值，以及EBO终点比较均未证。
本篇不修改旧候选，也不把这种受typed启发的规则称作树侧唯一规则。
