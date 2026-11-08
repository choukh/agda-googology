# 固定完成折叠接口的完整ω源实例

把外层捕获接回接口逐字所需的旧HS源。HS证书任意，目标仍为
leg(forget(read ω))，没有擅自把遗忘往返改成字面恒等。实例覆盖
全部自然数分量；不提供ω+1或整个CompletionPsiLower记录。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableCompletionPsiOmega where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.GeneralOmegaCountableOuterCaptureIf using (point-root)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape; native-HS)
open import OCF.Align.GeneralOmegaCountableTypedValueReference using (reference-shape)
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (forget-read)
open import OCF.Align.GeneralOmegaCountableOuterCaptureActual using (whole-omega)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.OCFSpecBase as V

target-shape : Same (leg (B.forget (B.read omega))) (leg omega)
target-shape = leg-same (forget-read (L.≅-refl⁰ (B.read omega)))

source-canonical : ∀ (h : L.HS (B.read omega)) →
  B.forget (L.ψ⁰ (L.Ω (L.toLevel (B.read omega) h))) ≤ᵛ
  B.forget (L.ψ⁰ (L.Ω (height omega omega-legal)))
source-canonical h = B.forget-mono (V.≅→≼ (L.ψ⁰-≅ (L.Ω-≅
  (L.toLevel-≅ h (native-HS omega omega-legal) (L.≅-refl⁰ (B.read omega))))))

target-canonical :
  B.forget (L.ψ⁰ (L.Ω (height (leg omega) (Lg-leg omega)))) ≤ᵛ
  B.forget (L.ψ⁰ (L.Ω (height (leg (B.forget (B.read omega)))
    (Lg-leg (B.forget (B.read omega))))))
target-canonical = B.forget-mono (V.≅→≼ (L.ψ⁰-≅ (L.Ω-≅
  (L.≅ᴵ-sym (height-shape target-shape
    (Lg-leg (B.forget (B.read omega))) (Lg-leg omega))))))

omega-lower : ∀ (h : L.HS (B.read omega)) →
  B.forget (L.ψ⁰ (L.Ω (L.toLevel (B.read omega) h))) ≤ᵛ
  B.forget (L.ψ⁰ (L.Ω (height (leg (B.forget (B.read omega)))
    (Lg-leg (B.forget (B.read omega))))))
omega-lower h = ≤-trans (source-canonical h)
  (≤-trans (same-value (reference-shape omega omega-legal (z⊲ᴮ omega)))
    (≤-trans whole-omega
      (≤-trans (same-value (same-sym
        (reference-shape (leg omega) (Lg-leg omega) (z⊲ᴮ (leg omega))))) target-canonical)))
```

此结论直接比较折叠输出的值，允许原ω与完成ω的基本列不同。
旧前驱包含在此并非所需前提；后继内部反馈仍是尚待解决的义务。
