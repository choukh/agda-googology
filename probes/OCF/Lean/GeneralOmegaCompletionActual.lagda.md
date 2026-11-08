# 所有实际后继层raw的完成不改序数值

纯动作在基值至少1时支配输入坐标。因此实际后继回调Aff(a)(leg d)
捕获完成坐标，闭包定理无需a合法。最后仅以Same运输值及leg的值，
不以Same运输第一位置或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCompletionActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Lean.LHRecTy using (ls)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.GeneralOmegaCompletionIf
open import OCF.Lean.GeneralOmegaConsumeLayerIf using (A; H; closure)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (whole; leg-same; positive)
import OCF.Lean.GeneralOmegaCompletionRun as Proof
import OCF.Lean.GeneralOmegaConsumeRun as R
import OCF.Lean.BoundedMixedAffine as Aff

affine-positive : ∀ a → hs hz ≤ᵛ a → ∀ d → hs hz ≤ᵛ Aff.Action.run S⊥ a d
affine-positive a p hz = p
affine-positive a p (hs d) = ≤l 0 (affine-positive a p d)
affine-positive a p (hl f) = ≤l 0 (affine-positive a p (f 0))
affine-positive a p (hΩ () f)
affine-inflate : ∀ a → hs hz ≤ᵛ a → ∀ d → d ≤ᵛ Aff.Action.run S⊥ a d
affine-inflate a p hz = z≤
affine-inflate a p (hs d) = ≤l 1 (add-mono (affine-inflate a p d) (affine-positive a p d))
affine-inflate a p (hl f) = l≤ (λ n → ≤l n (affine-inflate a p (f n)))
affine-inflate a p (hΩ () f)

captured : ∀ a → hs hz ≤ᵛ a → Capture (H a)
captured a p = record { on-chain = λ n → affine-inflate a p _ }
closure-upper : ∀ a → hs hz ≤ᵛ a → leg (closure a) ≤ᵛ closure a
closure-upper a p = Proof.Result.upper (H a) (captured a p)
closure-lower : ∀ a → closure a ≤ᵛ leg (closure a)
closure-lower a = inflation (closure a)

successor-upper : ∀ x → leg (R.run (ls x) (flL (ls x))) ≤ᵛ R.run (ls x) (flL (ls x))
successor-upper x = ≤-trans (same-value (leg-same (whole x)))
  (≤-trans (closure-upper (A x) (positive (ls x) (up (flL x))))
    (same-value (same-sym (whole x))))
successor-lower : ∀ x → R.run (ls x) (flL (ls x)) ≤ᵛ leg (R.run (ls x) (flL (ls x)))
successor-lower x = inflation _
```

每个x都是原实际后继地板实例，正性由原run给出，不是空前提。
本篇控制完成对这些完整输出的序数值；不声称FGH一致、跨up值一致，
也不将所有后继层保值外推到原ΛL的全部Ω指标层及ℕ极限总输出。
