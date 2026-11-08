# 第二站与实际WfFsn参照的连接

> 本文件的直接具体化第 2 站版本为草案：原闭包与分离轻核心后两次 6G 均退出 251（堆耗尽），本文件不计为定理。后来通过变量 k 的 opaque 封装，实际 Wf 第二站的值桥已在 BoundedCompletionStageWfOpaque / BoundedCompletionStageWfBridge 以 6G 编译通过；这里的失败不涉及那两个新模块。实际第二站包含于 EBO-tree 的证明仍未完成。

验收专用。复用既有HC/Lab唯一性比较参照，不展开记号良基证明计算分支。
编译使用/private/tmp/lambda-target-arch临时只读归档副本，不改archive。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWf where
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.Level using (Ordᶜ; zero; _≅_; ≅-sym)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.AccTreeLab using (HC; treeᴴ; labᴴ)
import OCF.Align.EBO as E
import OCF.Align.WfFsn as W
import OCF.Align.Value as V
import OCF.Align.OCFSpecBase as S
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionStageCore as F

-- 对任意HC证明成立，具体WfFsn证书是下文的实际实例。
hc-correspondence : ∀ (hc : HC (E.EBOψ 2)) → B.read F.reference ≅ treeᴴ hc
hc-correspondence hc = Lab-uniq F.reference-label (labᴴ hc)

opaque
  actual-stage : Ordᶜ zero
  actual-stage = treeᴴ (W.S.hc (W.S.p-tower 2))

  actual-reference : Cd
  actual-reference = B.forget actual-stage

  actual-label : Lab actual-stage (E.EBOψ 2)
  actual-label = W.ebo-lab 2

  actual-correspondence : B.read F.reference ≅ actual-stage
  actual-correspondence = hc-correspondence (W.S.hc (W.S.p-tower 2))

  actual≤EBO : actual-stage V.≼ W.EBO-tree
  actual≤EBO = V.≼l 2 (V.≼-refl actual-stage)

  lightweight≤actual : F.reference ≤ᵛ actual-reference
  lightweight≤actual = ≤-trans (B.roundtrip≥ F.reference)
    (B.forget-mono (S.≅→≼ actual-correspondence))

  actual≤lightweight : actual-reference ≤ᵛ F.reference
  actual≤lightweight = B.reference-lower-reflect (S.≅→≼ (≅-sym actual-correspondence))

lower-sound : ∀ {candidate : Cd} → F.reference ≤ᵛ candidate → actual-stage V.≼ B.read candidate
lower-sound p = V.≼-trans (V.≅→≼ (≅-sym actual-correspondence)) (Order.forward (B.read-mono p))
lower-reflect : ∀ {candidate : Cd} → actual-stage V.≼ B.read candidate → F.reference ≤ᵛ candidate
lower-reflect p = B.read-reflect (Order.backward (V.≼-trans (V.≅→≼ actual-correspondence) p))

reference≤EBO : B.read F.reference V.≼ W.EBO-tree
reference≤EBO = V.≼-trans (V.≅→≼ actual-correspondence) actual≤EBO

whole-family-sound : ∀ {candidate : Cd} → (∀ n → F.family n ≤ᵛ candidate) → actual-stage V.≼ B.read candidate
whole-family-sound h = lower-sound (F.family-cover h)
```

实际第二站、Cd参照、轻量参照的双向桥与EBO-tree里的第2分支关系均已
明确。whole-family-sound仍未在C上填完；StageFamily.first≤completed只解决首项。
本篇不宣称第二站已成为C的下界，更不把第二站当作EBO终点。

成功替代入口：`BoundedCompletionStageWfEbo` 已以 6G 编译通过，证明实际所有阶段包含于原 EBO-tree、第二站轻参照到 EBO 的下界，以及全实际阶段覆盖与终点下界的双向转换。本文件原版本的 251 状态不变。
