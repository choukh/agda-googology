# 全可数高度的真实后继输出公式

先在低层原HB中以Rel耦合全部反馈，再由跨up观察保持降到Cd。
不将高层Same或≤ᵛ直接喂给观察器。B可以是任意合法可数极限，
其中floor仍为原累计地板。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableSuccessorRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (rawΓ)
open import OCF.Lean.GeneralOmegaCountableRelIf using (Rel)
open import OCF.Lean.GeneralOmegaCountableRelRun using (floor-related)
open import OCF.Lean.GeneralOmegaCountableRelActual using (zero-same)
open import OCF.Lean.GeneralOmegaCountableObserveUp using (up-observe)
import OCF.Lean.GeneralOmegaCountableTopRun as Top
import OCF.Lean.GeneralOmegaCountableSuccessorIf as I
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-sym; same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

module At (B : Cd) (lB : LgB B) where
  open I.At B lB
  coordinates-back : ∀ i → Rel B (P.NoSum i) (coordinates i)
  coordinates-back zero = floor-related B
  coordinates-back (suc i) = Top.At.typed-back B lB (coordinates-back i)
  outputs : ∀ i → Same (emit (coordinates i)) (read-orbit i)
  outputs i = same-sym (zero-same (up-observe B lB hz (z⊲ᴮ B) (coordinates-back i)))

whole : ∀ B lB → Same
  (observe (hs B) lB hz (hsuc (z⊲ᴮ B)) (floor (hs B)))
  (hl (I.At.read-orbit B lB))
whole B lB rewrite I.root B lB = ll (At.outputs B lB)

gamma-whole : ∀ c → Same (rawΓ (hs c))
  (hl (I.At.read-orbit (leg c) (Lg-leg c)))
gamma-whole c = whole (leg c) (Lg-leg c)
gamma-lower : ∀ c → hl (I.At.read-orbit (leg c) (Lg-leg c)) ≤ᵛ rawΓ (hs c)
gamma-lower c = same-value (same-sym (gamma-whole c))
gamma-upper : ∀ c → rawΓ (hs c) ≤ᵛ hl (I.At.read-orbit (leg c) (Lg-leg c))
gamma-upper c = same-value (gamma-whole c)
```

gamma-whole是原rawΓ(hs c)的完整无限列公式，不是只选首项，也不是
重新定义一个同名Γ。它不提供Γ在任意输入值关系上的单调性。
