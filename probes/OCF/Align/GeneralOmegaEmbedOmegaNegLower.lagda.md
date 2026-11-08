# 原完整候选的有限重复全族下界

配对值审计使用已证明的实际阶段增长，不由Λ源名猜强度。以完整旧
Old.TΩ1为起点，反复取树上的ω重复；每个有限重复都进入原ΣF输出的
对应阶段。因此整可数族是原raw与完成树的真实值下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaEmbedOmegaNegLower where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l; s≤s; z≤)
open import OCF.Lean.Fold1Base using (≤-trans; ≤-refl)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.GeneralOmegaIndexRaise using (repeat-mono)
import OCF.Align.GeneralOmegaIndexOperationalActual as Actual
import OCF.Align.GeneralOmegaConsumeValueClosed as First
import OCF.Lean.GeneralOmegaConsumeClosed as Closed
import OCF.Lean.Fold1 as Old

reference : ℕ → Cd
reference zero = Old.TΩ1
reference (suc n) = Ops.repeat S⊥ (reference n)

stage-lower : ∀ n → reference n ≤ᵛ Actual.stage (suc n)
stage-lower zero = First.first
stage-lower (suc n) = ≤-trans (repeat-mono (stage-lower n)) (Actual.growth (suc n))

raw-lower : hl reference ≤ᵛ Closed.raw
raw-lower = l≤ (λ n → ≤l (suc n) (stage-lower n))
closed-lower : hl reference ≤ᵛ Closed.tree
closed-lower = ≤-trans raw-lower Closed.raw-lower

old-positive : hs hz ≤ᵛ Old.TΩ1
old-positive = ≤l zero (s≤s z≤)
strict-first : hs Old.TΩ1 ≤ᵛ reference 1
strict-first = ≤l 1 (add-mono (≤-refl Old.TΩ1) old-positive)
strict-closed : hs Old.TΩ1 ≤ᵛ Closed.tree
strict-closed = ≤-trans strict-first (≤-trans (≤l 1 (≤-refl _)) closed-lower)
not-bounded-by-first : Closed.tree ≤ᵛ Old.TΩ1 → ⊥
not-bounded-by-first p = ¬s≤ᵛ Old.TΩ1 (≤-trans strict-closed p)
```

证明量化全部n；reference是下界参照，没有替换原stage、run或闭项。
这里不新增记号标签或EBO验收，不声称该下界是候选的精确值或上界。
此前完成保值允许把候选大小研究集中在原raw，但本证明不需要把任意
值序穿过leg。名称中的Neg前缀表示配对路线归属，本篇结论是正面下界。
