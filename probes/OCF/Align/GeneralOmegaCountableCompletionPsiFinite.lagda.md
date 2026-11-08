# 完成下界接口的全部有限源实例

验收专用。每个自然数源的完成保持原树形，因此可对任意旧HS证书
给出接口结论。这里只填有限源，不将其当作CompletionPsiLower实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableCompletionPsiFinite where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Lean.GeneralOmegaCountableNumber using (leg-num)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (same-trans; leg-same)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape; native-HS)
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (forget-read)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.OCFSpecBase as V

numeric-shape : ∀ n → Same (leg (B.forget (B.read (num n)))) (num n)
numeric-shape n = same-trans (leg-same (forget-read (L.≅-refl⁰ (B.read (num n))))) final
  where
  final : Same (leg (num n)) (num n)
  final rewrite leg-num n = same-refl _

finite-lower : ∀ n (h : L.HS (B.read (num n))) →
  B.forget (L.ψ⁰ (L.Ω (L.toLevel (B.read (num n)) h))) ≤ᵛ
  B.forget (L.ψ⁰ (L.Ω (height (leg (B.forget (B.read (num n))))
    (Lg-leg (B.forget (B.read (num n)))))))
finite-lower n h = B.forget-mono (V.≅→≼ (L.ψ⁰-≅ (L.Ω-≅
  (L.≅ᴵ-trans
    (L.toLevel-≅ h (native-HS (num n) (num-legal n)) (L.≅-refl⁰ (B.read (num n))))
    (L.≅ᴵ-sym (height-shape (numeric-shape n)
      (Lg-leg (B.forget (B.read (num n)))) (num-legal n)))))))

actual-finite : ∀ n →
  B.forget (L.ψ⁰ (L.Ω (height (num n) (num-legal n)))) ≤ᵛ
  B.forget (L.ψ⁰ (L.Ω (height (leg (B.forget (B.read (num n))))
    (Lg-leg (B.forget (B.read (num n)))))))
actual-finite n = finite-lower n (native-HS (num n) (num-legal n))
```
