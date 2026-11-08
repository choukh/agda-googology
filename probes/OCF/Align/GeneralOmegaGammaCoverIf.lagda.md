# 允许升层的真实γ回调覆盖

验收专用。目标层x是显式参数，不要求它等于旧同源source t，也不把
层名相同当成值相同。比较的是原run的完整地板输出。这里比较可数
输出值，不选择或判定层下标；不引入裸下标比较律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaCoverIf where
open import OCF.Lean.LHRecTy using (LH)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaGammaIf using (reference; source)
open import OCF.Align.GeneralOmegaGammaRun using (one-lower)

record Cover (t : L.Ordᶜ L.zero) (h : L.HS t) (x : LH) : Set where
  field
    lower : reference t h ≤ᵛ run x (flL x)

one : Cover (L.suc L.zero) (L.hs L.hz) (source (L.suc L.zero))
one = record { lower = one-lower }
```

one消费已经证明的全部旧纯反馈轨道，不是有限测试。它只给非空实例；
没有据此给全t或原γ₂的Cover。后续可以更换x，不反过来改旧树、code
或证书。ψ₀(Ω_ω)的完整首回调需要全有限下标族，另篇精确校准。
