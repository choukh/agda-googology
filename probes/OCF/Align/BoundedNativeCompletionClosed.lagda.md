# 原生研究输出的合法可数完成项

这是一棵新研究树：完成原countable-output。原输出及其未完成的合法
证明义务仍保留。此处交付合法闭项与严格旧下界，EBO验收另待证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCompletionClosed where
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeValueStrict as V
import OCF.Lean.Fold1 as Old

tree : Cd
tree = leg N.countable-output
legal-tree : LgB tree
legal-tree = Lg-leg N.countable-output

raw-lower : N.countable-output ≤ᵛ tree
raw-lower = inflation N.countable-output

strict-old-lower : hs Old.TΩ1 ≤ᵛ tree
strict-old-lower = ≤-trans V.strict-old-lower raw-lower

not-bounded-by-old : tree ≤ᵛ Old.TΩ1 → ⊥
not-bounded-by-old p = ¬s≤ᵛ Old.TΩ1 (≤-trans strict-old-lower p)
```

tree只含布劳威尔0、后继、合法ℕ极限，且无接口参数。完成的序数值
可能大于原研究输出；尚未给上界、EBO下界或与原输出同值。禁止把
严格旧下界擅自读成ε₀、ψ₀Λ或其它未经验收的记号强度。
翻译账：leg沿用树侧累加规则，使用它的理由是实际合法性缺口；本篇
新开实验树，不替换任何旧定义，也不由值验收逼改原折叠。
