# 完成下界接口到原完整γ₂的条件应用

本篇明确以CompletionPsiLower为前提；不声称该接口已实现。两次
完成分别使用其字段，read/forget的差异只由结构Same和height-shape
运输，不抹掉双leg，也不把两份合法证默认判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableCompletionPsiTarget where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (Same; same-value)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape; native-HS)
open import OCF.Align.GeneralOmegaCountableTypedValueReference using (reference-shape)
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (forget-read)
open import OCF.Align.GeneralOmegaCountableCompletionPsiIf
import OCF.Align.GeneralOmegaCountableNextValueActual as A
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.OCFSpecBase as V
import OCF.Align.NoCumsum as N

forget-read-shape : ∀ c → Same (B.forget (B.read c)) c
forget-read-shape c = forget-read (L.≅-refl⁰ (B.read c))

module Conditional (completion : CompletionPsiLower) where
  c : Cd
  c = leg (B.forget (N.γ 1))
  first : B.forget (N.γ 2) ≤ᵛ B.forget (L.ψ⁰ (L.Ω (height c (Lg-leg (B.forget (N.γ 1))))))
  first = CompletionPsiLower.lower completion (N.γ 1) (N.cert 1)
  second : B.forget (L.ψ⁰ (L.Ω (height c (Lg-leg (B.forget (N.γ 1)))))) ≤ᵛ
    B.forget (L.ψ⁰ (L.Ω (height A.height (Lg-leg c))))
  second = ≤-trans
    (CompletionPsiLower.lower completion (B.read c) (native-HS c (Lg-leg (B.forget (N.γ 1)))))
    (B.forget-mono (V.≅→≼ (L.ψ⁰-≅ (L.Ω-≅
      (height-shape (leg-same (forget-read-shape c))
        (Lg-leg (B.forget (B.read c))) (Lg-leg c))))))
  γ₂≤auxiliary : B.forget (N.γ 2) ≤ᵛ A.auxiliary
  γ₂≤auxiliary = ≤-trans first (≤-trans second (≤-trans
    (same-value (reference-shape A.height (Lg-leg c) (z⊲ᴮ A.height))) (inflation _)))
  γ₂≤stage2 : B.forget (N.γ 2) ≤ᵛ C.stage 2
  γ₂≤stage2 = ≤-trans γ₂≤auxiliary A.auxiliary≤stage2
  γ₂≤tree : B.forget (N.γ 2) ≤ᵛ C.tree
  γ₂≤tree = ≤-trans γ₂≤auxiliary A.auxiliary≤tree
```

这里的γ₂是原NoCumsum完整第二项，未改成新参数族。唯一新增前提
是整个CompletionPsiLower；有限源或ω的个别实例不能填该前提。
即使前提成立，NoCumsum全γ链也只是EBO第二站所用链，不是EBO全塔。
