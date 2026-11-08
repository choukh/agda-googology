# 合法重定位闭项支配原Old3完整值

使用跨运行器的全部输出比较，并沿原部分和归纳。最终完成只用于
交付合法树及保留原值下界，未当作原输出同值或上界证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseCountableValue where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
import OCF.Lean.RebaseCountableClosed as D
open import OCF.Lean.RebaseCountableOrigin using (levels-actual; strict-third)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedWorldRebaseLowActual as Bridge
import OCF.Lean.Fold1 as Old

outputs : ∀ n → Whole.Model.oo n ≤ᵛ D.output n
outputs n rewrite levels-actual n = Bridge.outputs n
sums : ∀ n → Whole.Model.oO n ≤ᵛ Σ₀ D.output n
sums zero = outputs zero
sums (suc n) = add-mono (sums n) (outputs (suc n))

old3≤raw : Old.TΩ (num 3) tt ≤ᵛ D.raw
old3≤raw = ≤-trans (same-value Whole.old-three) (l≤ (λ n → ≤l n (sums n)))
old3≤tree : Old.TΩ (num 3) tt ≤ᵛ D.tree
old3≤tree = ≤-trans old3≤raw D.raw-lower
strict-old2 : hs (Old.TΩ (num 2) tt) ≤ᵛ D.tree
strict-old2 = ≤-trans strict-third old3≤tree
not-bounded-by-old2 : D.tree ≤ᵛ Old.TΩ (num 2) tt → ⊥
not-bounded-by-old2 p = ¬s≤ᵛ (Old.TΩ (num 2) tt) (≤-trans strict-old2 p)
```

本路线现交付(a)无参数合法闭项及其树上FGH，(b)原Old3完整下界与
严格Old2下界。Old3的记号读法未验收；没有D与原C的比较、D上界或
EBO全阶段下界，不能将D命名为ψ₀Λ或据此声称超过既有全部成果。
