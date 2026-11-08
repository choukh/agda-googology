# ψ₀(Ω₂)的完整typed观察值验收

本篇观察器含记号，只用于验收，不进入成品定义或证书。高层输入
是已有树侧Prototype的真实NoSum整族，既不换seed，也不增加累加。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedActual where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase using (Cd; HB; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaCoverFinite as F
import OCF.Align.GeneralOmegaGammaActual as G
open import OCF.Align.GeneralOmegaFiniteTypedIf
open import OCF.Align.GeneralOmegaFiniteTypedRun using (whole)

observe : HB U → Cd
observe a = B.forget (L.ψ⁰ (read a))
observed : Cd
observed = hl (λ n → observe (P.NoSum n))

reference≤observed : F.finite 2 ≤ᵛ observed
reference≤observed = B.forget-mono (V.≅→≼ whole)
observed≤reference : observed ≤ᵛ F.finite 2
observed≤reference = B.forget-mono (V.≅→≼ (L.≅-sym whole))
```

两条界核准的是ψ₀(Ω₂)，并非只重复ψ₀(Ω₁)锚点。但observed不是新
消费者输出：这不是ψ₀(Ω₂)≤GeneralOmegaConsumeClosed.tree。
下一义务是把这些完整观察值与更高ΩL源的真实回调关联；原typed
高层的whole-cover不能替代那条外层观察模拟。
