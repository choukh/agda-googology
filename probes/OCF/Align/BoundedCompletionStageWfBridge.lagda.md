# 实际Wf第二站与轻参照的值连接

使用已封装的实际阶段标签，以Lab唯一性连接，不展开具体HC证明，
也不在本篇提取EBO-tree的第2分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWfBridge where
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.Level using (_≅_; ≅-sym)
open import OCF.Align.Stage2 using (Lab-uniq)
import OCF.Align.Value as V
import OCF.Align.OCFSpecBase as S
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionStageCore as F
import OCF.Align.BoundedCompletionStageWfOpaque as W

actual-correspondence : B.read F.reference ≅ W.stage2
actual-correspondence = Lab-uniq F.reference-label W.stage2-label

actual-reference : Cd
actual-reference = B.forget W.stage2
lightweight≤actual : F.reference ≤ᵛ actual-reference
lightweight≤actual = ≤-trans (B.roundtrip≥ F.reference)
  (B.forget-mono (S.≅→≼ actual-correspondence))
actual≤lightweight : actual-reference ≤ᵛ F.reference
actual≤lightweight = B.reference-lower-reflect (S.≅→≼ (≅-sym actual-correspondence))

lower-sound : ∀ {candidate : Cd} → F.reference ≤ᵛ candidate → W.stage2 V.≼ B.read candidate
lower-sound p = V.≼-trans (V.≅→≼ (≅-sym actual-correspondence)) (Order.forward (B.read-mono p))
lower-reflect : ∀ {candidate : Cd} → W.stage2 V.≼ B.read candidate → F.reference ≤ᵛ candidate
lower-reflect p = B.read-reflect (Order.backward (V.≼-trans (V.≅→≼ actual-correspondence) p))

whole-family-sound : ∀ {candidate : Cd} → (∀ n → F.family n ≤ᵛ candidate) → W.stage2 V.≼ B.read candidate
whole-family-sound h = lower-sound (F.family-cover h)
```

实际第2站与轻量Cd参照的双向值界、候选下界的双向转换都有具体实例。
仍未证明C覆盖整族，不声称C已达到此站或ψ₀Λ。
