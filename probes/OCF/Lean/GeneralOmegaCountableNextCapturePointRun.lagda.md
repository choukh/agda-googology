# 逐点种子到原累计种子的完整反馈模拟

对有向Sim推导递归；零分支直接对右source证明pointFloor下界，
不假设Sim传递。每个反馈坐标由point-floor和iterate-sim完整耦合。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableNextCapturePointRun where
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor; point-floor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareClass
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure
open import OCF.Lean.GeneralOmegaCountableRegularCompareRun using (node-lower)

point-positive : ∀ B lB t pt a → Sim t (pointFloor t) (observe B lB t pt a)
point-positive B lB t pt hz = point-floor t
point-positive B lB t pt (hs a) = sli 1 (point-positive B lB t pt a)
point-positive B lB t pt (hl f) = sli 0 (point-positive B lB t pt (f 0))
point-positive B lB t pt (hΩ κ f) = node-lower pt (classify B lB t pt κ)
  (λ i pi e → observe B lB i pi (f e)) (λ e → point-positive B lB t pt (f e))

mixed-node : ∀ {B t A} (Q : A → A → Set) (pt : t ⊲ B) (v : C.Dc F B t A) → Good Q v →
  (rec rec′ : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ r pr {a b} → Q a b → Sim r (rec r pr a) (rec′ r pr b)) →
  Sim t (point-node pt v rec) (node pt v rec′)
mixed-node Q pt (C.keep κ fr) good rec rec′ rel = so (λ r → rel _ pt (good r))
mixed-node {t = t} Q pt (C.same to) good rec rec′ rel = sl (λ n → rel t pt
  (good (iterate-sim (λ r → rel t pt (good r)) (point-floor t) n)))
mixed-node {t = t} Q pt (C.above i pi ti to) good rec rec′ rel = sl (λ n → rel t pt
  (good (iterate-sim (λ r → rel i (⊲ᴮ-tr (hsuc hself) pi) (good r)) (point-floor i) n)))

simulate : ∀ B lB t pt {a b} → Sim B a b → Sim t (point-observe B lB t pt a) (observe B lB t pt b)
simulate B lB t pt (sz {b}) = point-positive B lB t pt b
simulate B lB t pt (ss p) = sl (left-sim (simulate B lB t pt p))
simulate B lB t pt (sr p) = sli 1 (simulate B lB t pt p)
simulate B lB t pt (sl p) = sl (λ n → simulate B lB t pt (p n))
simulate B lB t pt (sli n p) = sli n (simulate B lB t pt p)
simulate B lB t pt (so {κ} {f} {g} p) = mixed-node (Coordinate B κ) pt
  (classify B lB t pt κ) (class-good B lB t pt κ)
  (λ i pi e → point-observe B lB i pi (f e)) (λ i pi e → observe B lB i pi (g e))
  (λ i pi r → simulate B lB i pi (p r))
simulate B lB t pt (sor {κ = κ} {g} p) = node-lower pt (classify B lB t pt κ)
  (λ i pi e → observe B lB i pi (g e)) (λ e → simulate B lB t pt (p e))
instance-point : PointSimulation
instance-point = record { simulate = simulate }
```

same和above的初始关系均为真实point-floor；keep使用原class-good
运回异坐标关系。没有将任意Same喂给高层分支，未省略反馈seed差异。
