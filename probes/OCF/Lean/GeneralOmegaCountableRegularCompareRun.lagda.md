# 原观察保持有向模拟

零点所需floor下界对原每个输出直接构造；保留Ω时使用全部枝的
统一下界。同层/高层反馈以原floor自证开始，只消费已给异坐标关系。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareRun where
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareClass
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure

node-lower : ∀ {B t A a} (pt : t ⊲ B) (v : C.Dc F B t A)
  (rec : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ e → Sim t a (rec t pt e)) → Sim t a (node pt v rec)
node-lower pt (C.keep κ fr) rec p = sor (λ e → p (fr e))
node-lower pt (C.same to) rec p = sli 0 (p (to (floor _)))
node-lower pt (C.above i pi ti to) rec p = sli 0 (p (to (floor i)))
positive : ∀ B lB t pt a → Sim t (floor t) (observe B lB t pt a)
positive B lB t pt hz = floor-self t
positive B lB t pt (hs a) = sli 1 (positive B lB t pt a)
positive B lB t pt (hl f) = sli 0 (positive B lB t pt (f 0))
positive B lB t pt (hΩ κ f) = node-lower pt (classify B lB t pt κ)
  (λ i pi e → observe B lB i pi (f e)) (λ e → positive B lB t pt (f e))

node-compare : ∀ {B t A} (Q : A → A → Set) (pt : t ⊲ B) (v : C.Dc F B t A) → Good Q v →
  (rec rec′ : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ r pr {a b} → Q a b → Sim r (rec r pr a) (rec′ r pr b)) →
  Sim t (node pt v rec) (node pt v rec′)
node-compare Q pt (C.keep κ fr) good rec rec′ rel = so (λ r → rel _ pt (good r))
node-compare {t = t} Q pt (C.same to) good rec rec′ rel = sl (λ n → rel t pt
  (good (iterate-sim (λ r → rel t pt (good r)) (floor-self t) n)))
node-compare {t = t} Q pt (C.above i pi ti to) good rec rec′ rel = sl (λ n → rel t pt
  (good (iterate-sim (λ r → rel i (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-self i) n)))

compare : ∀ B lB t pt {a b} → Sim B a b → Sim t (observe B lB t pt a) (observe B lB t pt b)
compare B lB t pt (sz {b}) = positive B lB t pt b
compare B lB t pt (ss p) = sl (left-sim (compare B lB t pt p))
compare B lB t pt (sr p) = sli 1 (compare B lB t pt p)
compare B lB t pt (sl p) = sl (λ n → compare B lB t pt (p n))
compare B lB t pt (sli n p) = sli n (compare B lB t pt p)
compare B lB t pt (so {κ} {f} {g} p) = node-compare (Coordinate B κ) pt
  (classify B lB t pt κ) (class-good B lB t pt κ)
  (λ i pi e → observe B lB i pi (f e)) (λ i pi e → observe B lB i pi (g e))
  (λ i pi r → compare B lB i pi (p r))
compare B lB t pt (sor {κ = κ} {g} p) = node-lower pt (classify B lB t pt κ)
  (λ i pi e → observe B lB i pi (g e)) (λ e → compare B lB t pt (p e))
instance-structural : StructuralComparison
instance-structural = record { floor-self = floor-self ; compare = compare ; complete = complete }
```
