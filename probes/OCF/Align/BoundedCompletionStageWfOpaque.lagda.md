# 在变量阶段检查实际Wf参照

opaque块内只对变量k定义阶段与标签，块外取第2站，避免在透明区
规范化巨大的具体p-tower 2证书。这没有改变实际Wf参照。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWfOpaque where
open import Data.Nat using (ℕ)
open import OCF.Align.Level using (Ordᶜ; zero)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.AccTreeLab using (treeᴴ)
import OCF.Align.EBO as E
import OCF.Align.WfFsn as W

opaque
  stage : ℕ → Ordᶜ zero
  stage k = treeᴴ (W.S.hc (W.S.p-tower k))

  stage-label : ∀ k → Lab (stage k) (E.EBOψ k)
  stage-label k = W.ebo-lab k

stage2 : Ordᶜ zero
stage2 = stage 2
stage2-label : Lab stage2 (E.EBOψ 2)
stage2-label = stage-label 2
```

这里只给实际每站及标签，不展开EBO-tree的分支，也未给候选下界。
