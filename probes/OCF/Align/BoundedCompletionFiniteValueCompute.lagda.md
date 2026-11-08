# 实际坐标动作的全结构计算与初界覆盖

本篇消费SelfKeep的点态坐标证据；实例由独立重建文件提供。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueCompute where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans; ≤⊞)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
import OCF.Lean.BoundedDiagonalSame as SameTool
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionFinitePlaceDecision
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueIf
open import OCF.Align.BoundedCompletionFiniteValueKeep
open import OCF.Align.BoundedCompletionFiniteValueAffine
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ

open import OCF.Lean.TowerCollapseIf using (module Ops)

same-partial : ∀ {S} {a b : HB S} → Same a b → ∀ n →
  Same (Ops.partial S (λ _ → a) n) (Ops.partial S (λ _ → b) n)
same-partial p zero = p
same-partial p (suc n) = SameTool.same-add (same-partial p n) p

module From (sk : SelfKeep) where
  open SelfKeep sk
  up-run : ∀ n (a : HB (Native (num n))) → Same
    (at (suc n) n {B = num (suc n)} (legal-num (suc n)) hself (hsuc hself) (up a))
    (Affine.Action.run (Native (num n)) a)
  up-run n hz = ss zz
  up-run n (hs a) = ll (same-partial (up-run n a))
  up-run n (hl f) = ll (λ j → up-run n (f j))
  up-run n (hΩ κ g)
    with decide {B = num n} {t = num n} hself (legal-num n) (raise hself (classify (num n) κ))
       | decide {B = num (suc n)} {t = num n} (hsuc hself) (legal-num (suc n))
           (raise hself (raise (hsuc hself) (classify (num n) κ)))
       | up-component n n κ {B = num n} {B′ = num (suc n)} (legal-num n) (legal-num (suc n)) hself hself hself (hsuc hself)
       | self-keep n κ
  ... | .(keep κ fr) | .(keep κ fr) | kept .κ .fr | retained fr fe =
    oo (λ e → subst (λ d → Same
      (at (suc n) n {B = num (suc n)} (legal-num (suc n)) hself (hsuc hself) (up (g d)))
      (Affine.Action.run (Native (num n)) (g e)))
      (sym (fe e)) (up-run n (g e)))

  model-floor : ∀ n → floor n ≤ᵛ Θ.model n
  model-floor zero = right-add hz (floor zero)
  model-floor (suc n) = right-add (up (Θ.model n)) (floor (suc n))

  first-floor : ∀ n → floor n ≤ᵛ first n
  first-floor n = ≤-trans (model-floor n)
    (≤-trans (≤⊞ (Θ.model n) (hs hz))
      (≤-trans (Affine.inflation (Native (num n)) (Θ.model n ⊞ hs hz))
        (≤-trans (same-value (same-sym (up-run n (Θ.model n ⊞ hs hz))))
          (right-add (hs hz) (coordinate n (hs hz))))))

  instance-first : FirstFloor
  instance-first = record { first-floor = first-floor }
```
