# 原Γ迭代闭项的完整有限参照族下界

本篇仅作值验收，记号不进入闭项。新的树侧捕获定理把全部数值参数
输出送入原stage 2；此前逐有限高度的验收现在可以真正用于原迭代
闭项，而不再停留在另一个参数族。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableCaptureValue where
open import OCF.Lean.CRwBase using (hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
open import OCF.Lean.GeneralOmegaCountableCaptureRun using (finite-capture)
import OCF.Align.GeneralOmegaCountableFiniteAll as A
import OCF.Align.GeneralOmegaGammaCoverFinite as F
import OCF.Align.GeneralOmegaGammaActual as G

finite≤stage2 : ∀ n → F.finite n ≤ᵛ C.stage 2
finite≤stage2 n = ≤-trans (A.reference≤Γ n) (finite-capture n)
family≤stage2 : hl F.finite ≤ᵛ C.stage 2
family≤stage2 = l≤ finite≤stage2
first-callback≤stage2 : G.reference-branch 0 ≤ᵛ C.stage 2
first-callback≤stage2 = ≤-trans F.first≤finite family≤stage2
first-callback≤tree : G.reference-branch 0 ≤ᵛ C.tree
first-callback≤tree = ≤-trans first-callback≤stage2 (C.stage-lower 2)
```

结论是原合法Γ迭代闭项不低于γ₂的整个首回调，即ψ₀(Ω_ω)。
这是序数值下界，不是基本列或FGH一致；尚未覆盖完整γ₂的其他回调，
更没有据此宣称达到ψ₀Λ。没有使用一般Γ单调，也没有改变原运行器。
