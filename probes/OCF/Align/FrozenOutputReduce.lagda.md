# 完整第二分量比较的精确剩余义务

所有实际输出已接到模型；这里只剩生成域上的局部改界吸收。
下面结论带明确前提，不声称该前提已经证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputReduce where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l; ΣT)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf using (Generated; changing; frozen; actual-old-generated)
import OCF.Align.FrozenOutputIf as If
import OCF.Align.FrozenOutputModel as M
import OCF.Align.FrozenOutputBridge as B
import OCF.Align.FrozenValueSecond as S
import OCF.Lean.Fold1 as Original
import OCF.Lean.Fold1Fold as O
import OCF.Lean.SupCollapseFrozen as N
import OCF.Lean.SupCollapseClosed as C

open If.Model Original.TΩ1

module Reduce
  (absorb : ∀ c → Generated c → run changing hz c ≤ᵛ run frozen hz c) where

  outputs : ∀ n → S.Old.oo n ≤ᵛ S.Frozen.oo n
  outputs n = ≤-trans (same-value (B.old-output-model n))
    (≤-trans (absorb _ (actual-old-generated n))
      (≤-trans (same-value (M.Congruence.actual-coordinate-congruence Original.TΩ1 frozen hz n))
        (same-value (same-sym (B.frozen-output-model n)))))

  sums : ∀ n → S.Old.oO n ≤ᵛ S.Frozen.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))

  second : O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) S.W (ΣT S⊥ hz C.num 2)
    ≤ᵛ N.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) S.W (ΣT S⊥ hz C.num 2)
  second = l≤ (λ n → ≤l n (sums n))

  original-second≤frozen-Tω :
    O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) S.W (ΣT S⊥ hz C.num 2) ≤ᵛ C.Tω
  original-second≤frozen-Tω = ≤l 2 second
```

生成域已有无条件实际实例 `actual-old-generated`；吸收前提没有被假定为空真，
但其可满足性尚未证明，因此本模块只是归约定理。不能据此汇报完整第二分量下界
已经成立。下一步应证明或反驳 `absorb`，而不是继续逐个外层输出取样。
