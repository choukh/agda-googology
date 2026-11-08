# 实际各站到 EBO 的值包含

验收专用。只在变量阶段展开自有 opaque 阶段定义，避免具体第 2 站
的良基证明规范化。这里的 EBO 是原 WfFsn.EBO-tree。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWfEbo where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Align.WfFsn as E
import OCF.Align.Value as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableTarget as Target
import OCF.Align.BoundedCompletionStageCore as F
import OCF.Align.BoundedCompletionStageWfOpaque as W
import OCF.Align.BoundedCompletionStageWfBridge as Bridge

opaque
  unfolding W.stage
  stage≤EBO : ∀ k → W.stage k V.≼ E.EBO-tree
  stage≤EBO k = V.≼l k (V.≼-refl (W.stage k))

  stages-cover : ∀ {candidate : Cd} →
    (∀ k → W.stage k V.≼ B.read candidate) → E.EBO-tree V.≼ B.read candidate
  stages-cover h = V.l≼ h

stage2≤EBO : W.stage2 V.≼ E.EBO-tree
stage2≤EBO = stage≤EBO 2

light-reference≤EBO : B.read F.reference V.≼ E.EBO-tree
light-reference≤EBO = V.≼-trans (V.≅→≼ Bridge.actual-correspondence) stage2≤EBO

stage-Cd : ℕ → Cd
stage-Cd k = B.forget (W.stage k)

whole-stages-lower : ∀ {candidate : Cd} →
  (∀ k → stage-Cd k ≤ᵛ candidate) → Target.reference ≤ᵛ candidate
whole-stages-lower h = Target.lower-reflect (stages-cover
  (λ k → Order.forward (B.reference-lower (h k))))

whole-stages-necessary : ∀ {candidate : Cd} → Target.reference ≤ᵛ candidate →
  ∀ k → stage-Cd k ≤ᵛ candidate
whole-stages-necessary h k = B.reference-lower-reflect (Order.backward
  (V.≼-trans (stage≤EBO k) (Target.lower-sound h)))
```

全实际阶段的覆盖与实际 EBO 下界互相推出。尚未给成品 C 的全阶段
覆盖；第二站包含定理不反向声称 C 达到第二站。
