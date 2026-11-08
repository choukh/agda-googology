# 提高原源界并保留目标的完整观察模拟

本篇只比较B与hs B的原up注入，目标t和原t⊲B保持。旧kind的
cl/dcl分类在提高源界后逐字对应；above反馈路径只是原路径的hsuc。
因此可用遗传坐标关系同步完整反馈，不要求不同极限副本相干。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveUp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelClass
open import OCF.Lean.GeneralOmegaCountableRelRun

record UpSimulation : Set₁ where
  field
    full-up : ∀ B lB t pt {a b} → Rel B a b →
      Rel t (observe B lB t pt a) (observe (hs B) lB t (hsuc pt) (up b))

lift-decision : ∀ {B t A} → C.Dc F B t A → C.Dc F (hs B) t A
lift-decision (C.keep κ fr) = C.keep κ fr
lift-decision (C.same to) = C.same to
lift-decision (C.above i pi ti to) = C.above i (hsuc pi) ti to

lift-pick : ∀ {B t i A} (to : HB (F i) → A) (pi : hs i ⊲ B)
  (r : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  lift-decision (C.pick S⊥ to pi r) ≡ C.pick S⊥ to (hsuc pi) r
lift-pick to pi (inj₂ p) = refl
lift-pick to pi (inj₁ hself) = refl
lift-pick to pi (inj₁ (hsuc hself)) = refl
lift-pick to pi (inj₁ (hsuc (hsuc p))) = refl
lift-pick to pi (inj₁ (hsuc (hlim n p))) = refl
lift-pick to pi (inj₁ (hsuc (hLim {κ = ()} b p)))

classify-up : ∀ B (lB : LgB B) t (pt : t ⊲ B) κ →
  classify (hs B) lB t (hsuc pt) (inj₁ κ) ≡
  lift-decision (classify B lB t pt κ)
classify-up B lB t pt κ with C.cl B κ
... | C.bas () to
... | C.nw i pi to = sym (lift-pick to pi (cmpB pi pt tt lB))

lift-good : ∀ {B t A} {Q : A → A → Set} {v : C.Dc F B t A} →
  Good Q v → Good Q (lift-decision v)
lift-good {v = C.keep κ fr} p = p
lift-good {v = C.same to} p = p
lift-good {v = C.above i pi ti to} p = p

node-up : ∀ {B t A} (Q : A → A → Set) (pt : t ⊲ B) (v : C.Dc F B t A) → Good Q v →
  (rec : ∀ r → r ⊲ B → A → HB (F r)) →
  (rec′ : ∀ r → r ⊲ hs B → A → HB (F r)) →
  (∀ r pr {a b} → Q a b → Rel r (rec r pr a) (rec′ r (hsuc pr) b)) →
  Rel t (node pt v rec) (node (hsuc pt) (lift-decision v) rec′)
node-up Q pt (C.keep κ fr) good rec rec′ rel = ro (λ r → rel _ pt (good r))
node-up {t = t} Q pt (C.same to) good rec rec′ rel = rl (λ n → rel t pt
  (good (iterate-rel (λ r → rel t pt (good r)) (floor-related t) n)))
node-up {t = t} Q pt (C.above i pi ti to) good rec rec′ rel = rl (λ n → rel t pt
  (good (iterate-rel (λ r → rel i (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-related i) n)))

up-observe : ∀ B lB t pt {a b} → Rel B a b →
  Rel t (observe B lB t pt a) (observe (hs B) lB t (hsuc pt) (up b))
up-observe B lB t pt rz = floor-related t
up-observe B lB t pt (rs p) = rl (left-rel (up-observe B lB t pt p))
up-observe B lB t pt (rl p) = rl (λ n → up-observe B lB t pt (p n))
up-observe B lB t pt (ro {κ} {f} {g} p) = subst
  (λ v → Rel t (node pt (classify B lB t pt κ)
    (λ r pr e → observe B lB r pr (f e)))
    (node (hsuc pt) v (λ r pr e → observe (hs B) lB r pr (up (g e)))))
  (sym (classify-up B lB t pt κ))
  (node-up (Coord B κ) pt (classify B lB t pt κ) (class-good B lB t pt κ)
    (λ r pr e → observe B lB r pr (f e))
    (λ r pr e → observe (hs B) lB r pr (up (g e)))
    (λ r pr cd → up-observe B lB r pr (p cd)))

instance-up : UpSimulation
instance-up = record { full-up = up-observe }
```

floor-related为全高度输入实填前提；up-observe比较完整原输出，
适用于含ℕ极限的B。它只证明这一指定up及指定hsuc路径，不是
任意高度值序单调、路径无关或一般κ重排定理。
