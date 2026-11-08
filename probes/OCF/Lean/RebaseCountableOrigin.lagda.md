# 重定位闭项的原始输入及旧第三地板的严格下界

levels与原Whole最高回灌坐标逐项字面相等；不以相似模型替代输入。
另外校准旧第三地板首输出为完整Old2，并由下一输出恒正给严格界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseCountableOrigin where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-add)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedWorldValueTwoSlot using (low)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedWorldValueCoverIf as Middle
import OCF.Align.BoundedWorldValueCoverReduce as Reduce
import OCF.Align.BoundedCompletionValueAcceptOld as Old2
import OCF.Lean.Fold1 as Old
import OCF.Lean.RebaseCountableClosed as D
open import OCF.Lean.TwoSlotValueRun using (lower-positive)
open import OCF.Align.BoundedWorldSeedIf using (Seed1)
open import OCF.Align.BoundedWorldSeedActual using (old1-coordinates)

levels-actual : ∀ n → D.levels n ≡ Whole.Model.ce n
levels-actual zero = refl
levels-actual (suc n) rewrite levels-actual n = refl
levels-seed : ∀ n → Seed1 (D.levels n)
levels-seed n rewrite levels-actual n = old1-coordinates n

first-sums : ∀ n → Same (Middle.Middle.oO hz n) (Old2.Pure.oO n)
first-sums zero = Reduce.outputs hz zero
first-sums (suc n) = same-add (first-sums n) (Reduce.outputs hz (suc n))

first-output : Same (low hz (floor zero) (floor 1)) (hl Old2.Pure.oO)
first-output = ll first-sums
old2≤first : Old.TΩ (num 2) tt ≤ᵛ Whole.Model.oo zero
old2≤first = ≤-trans (same-value Old2.old2) (same-value (same-sym first-output))

strict-third : hs (Old.TΩ (num 2) tt) ≤ᵛ Old.TΩ (num 3) tt
strict-third = ≤-trans
  (≤l 1 (add-mono old2≤first (lower-positive hz (floor zero) (Whole.Model.ce 1))))
  (same-value (same-sym Whole.old-three))
```

strict-third是关于原合法旧闭项的值定理，不是其记号读法。D的下界仍需
把每个low输出与重定位实际运行相连，再比较全部原输出和。
