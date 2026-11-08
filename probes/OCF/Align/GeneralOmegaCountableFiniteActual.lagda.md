# 原可数高度Γ(num 2)的ψ₀(Ω₂)下界

验收专用。参照进入原可数高度运行器的真实num 2输入，没有改其
ℕ高度累计地板。这个参数实例是闭项；它不是Γ迭代覆盖定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteActual where
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Lean.GeneralOmegaCountableObserveClass as N
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
import OCF.Lean.GeneralOmegaFiniteObserveClosed as Fin
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaCoverFinite as F
import OCF.Align.GeneralOmegaFiniteTypedAllActual as Old
open import OCF.Align.GeneralOmegaCountableFiniteSecond using (whole)

reference≤raw : F.finite 2 ≤ᵛ C.rawΓ (N.num 2)
reference≤raw = B.reference-lower-reflect (V.≅→≼ whole)
raw≤reference : C.rawΓ (N.num 2) ≤ᵛ F.finite 2
raw≤reference = ≤-trans (B.roundtrip≥ (C.rawΓ (N.num 2)))
  (B.forget-mono (V.≅→≼ (L.≅-sym whole)))
finite≤countable : Fin.stage 2 ≤ᵛ C.rawΓ (N.num 2)
finite≤countable = ≤-trans Old.second≤reference reference≤raw
countable≤finite : C.rawΓ (N.num 2) ≤ᵛ Fin.stage 2
countable≤finite = ≤-trans raw≤reference Old.reference≤second
reference≤completed : F.finite 2 ≤ᵛ C.Γ (N.num 2)
reference≤completed = ≤-trans reference≤raw (inflation (C.rawΓ (N.num 2)))
```

已证rawΓ(num 2)与既有完整Finite.stage 2互相≤ᵛ，且合法Γ(num 2)
覆盖ψ₀(Ω₂)。尚未证明Γ迭代闭项C.tree覆盖Γ(num 2)：不能从一个
参数实例下界，或从Γ的名字，推出迭代实际访问或吸收这个输入。
全自然数高度的一致性及ℕ高度累计地板的记号界仍须另证。
