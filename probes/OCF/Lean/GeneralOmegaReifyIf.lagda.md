# typed反馈重化与实际首次访问接口

Reify沿原层算术，不增加专属节点。typed动作以原floor为零点并保留
全部旧Ω种类；不与新run的zero=1混同。访问项保留原θ累计前缀，
接口没有假定“可入即采样”或删除前缀后的运行单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaReifyIf where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; gcF; cxI)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.BoundedMixedAffine using (module Action)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Lean.GeneralOmegaConsumeRun as R

Reify : ∀ j → HB (Lv j) → LH
Reify j a = ΩL j ⊕L upL j a
Typed : ∀ j → HB (Lv j) → HB (Lv j)
Typed j = Action.run (Lv j) (flL j)
Orbit : ∀ j → ℕ → HB (Lv j)
Orbit j = Action.chain (Lv j) (flL j)
θ : ∀ j → HB (Lv j) → HB (Lv (ΩL (ls j)))
θ j = New.θ (cxI j (Reify j)) (gcF (λ a → ι {IxL j} {FXL j (Reify j)} (inj₂ a) (flL (Reify j a))))
VisitedFloor : ∀ j → HB (Lv (ΩL (ls j)))
VisitedFloor j = θ j (flL j) ⊞
  ι {IxL j} {FXL j (Reify j)} (inj₂ (flL j)) (flL (Reify j (flL j)))

record Reification : Set₁ where
  field
    orbit-legal : ∀ j n → LgB (Orbit j n)
    visited-legal : ∀ j → LgB (VisitedFloor j)
    visited-value : ∀ j → R.run (ΩL (ls j)) (VisitedFloor j) ≤ᵛ
      R.run (ΩL (ls j)) (flL (ΩL (ls j)))
```

该记录只给真实访问和typed域，不能替代typed整输出的有向覆盖。
下一缺口须比较Typed轨道与VisitedFloor后续真实回调，而非把它们
同名或用Same抹掉旧Ω。
