# 实际Wf第二站的标签桥

> 本文件的直接具体化第 2 站版本为草案：6G 退出 251，尚未通过。仅输出本模块 Checking，随后堆耗尽，未给声明级定位。后来变量 k 的 opaque 版本及实际第二站值桥已分别在 BoundedCompletionStageWfOpaque / BoundedCompletionStageWfBridge 以 6G 编译通过，本文件的失败不涉及新桥。

验收专用。只取实际第二站及既有标签，通过Lab唯一性连接轻参照；
不在本模块展开EBO-tree取第2支，也不具体应用HC递归比较函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWfLabel where
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.Level using (Ordᶜ; zero; _≅_; ≅-sym)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.AccTreeLab using (treeᴴ)
import OCF.Align.WfFsn as W
import OCF.Align.EBO as E
import OCF.Align.Value as V
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionStageCore as F

opaque
  actual-stage : Ordᶜ zero
  actual-stage = treeᴴ (W.S.hc (W.S.p-tower 2))

  actual-label : Lab actual-stage (E.EBOψ 2)
  actual-label = W.ebo-lab 2

actual-correspondence : B.read F.reference ≅ actual-stage
actual-correspondence = Lab-uniq F.reference-label actual-label

lower-sound : ∀ {candidate : Cd} → F.reference ≤ᵛ candidate → actual-stage V.≼ B.read candidate
lower-sound p = V.≼-trans (V.≅→≼ (≅-sym actual-correspondence)) (Order.forward (B.read-mono p))
lower-reflect : ∀ {candidate : Cd} → actual-stage V.≼ B.read candidate → F.reference ≤ᵛ candidate
lower-reflect p = B.read-reflect (Order.backward (V.≼-trans (V.≅→≼ actual-correspondence) p))
```

本篇不证明实际EBO-tree包含此分支，也不声明C已超过此第二站。

成功替代入口：`BoundedCompletionStageWfEbo` 已以 6G 编译通过，证明实际所有阶段包含于原 EBO-tree、第二站轻参照到 EBO 的下界，以及全实际阶段覆盖与终点下界的双向转换。本文件原版本的 251 状态不变。
