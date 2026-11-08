# 实际第一规范输出进入第二采样

直接保留完整 normal 1 的末段输出，不把它换成双 Ω 子样本。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputAcceptLift where
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Align.BoundedCompletionFiniteRunIf using (Rel)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (up-rel; pure-reflexive)
open import OCF.Align.BoundedCompletionFinitePlaceAny using (any-up)
open import OCF.Align.BoundedCompletionFinitePlacePER using (rel-trans)
open import OCF.Align.BoundedCompletionTerminalRel using (terminal-rel)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionFinitePlaceSample as Sample
import OCF.Align.BoundedCompletionValueAcceptModel as M
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeCompletionClosed as C

input : Rel hz (Θ.normal 1) (M.low (up (Θ.model 1)))
input = rel-trans hz
  (any-up 1 0 tt tt (hsuc hself) (hsuc (hsuc hself)) (Θ.model-rel 1)
    (N.component-path (hs hz) (hs hz) hself (Θ.model 1))
    (N.component-path (hs (hs hz)) (hs (hs hz)) hself (up (Θ.model 1))))
  (M.low-rel (up-rel (hs hz) (Θ.model-rel 1)))

whole-same : Same (T.fold V.feedback (Θ.normal 1))
  (T.fold V.feedback (M.low (up (Θ.model 1))))
whole-same = terminal-rel input (pure-reflexive V.feedback)

selected : T.fold V.feedback (M.low (up (Θ.model 1))) ≤ᵛ M.output
selected = ≤l 0 (≤l 0 (≤-refl _))

whole≤normalized : T.fold V.feedback (Θ.normal 1) ≤ᵛ Sample.normalized 1
whole≤normalized = ≤-trans (same-value whole-same)
  (≤-trans selected (same-value (same-sym M.actual-output)))
whole≤C : T.fold V.feedback (Θ.normal 1) ≤ᵛ C.tree
whole≤C = ≤-trans whole≤normalized (Sample.normalized-below-C 1)
```
