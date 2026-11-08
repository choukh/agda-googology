# 第二站参照与HC标准参照的值桥

验收专用。不展开具体WfFsn良基证书；对同一第二站的每个HC证书证明
参照一致，并给现成HC-BTBO的具体实例。直接Wf实例仍见标明251的草案。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageHC where
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.Level using (_≅_; ≅-sym)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.AccTreeLab using (HC; treeᴴ; labᴴ; HC-BTBO)
import OCF.Align.EBO as E
import OCF.Align.Value as V
import OCF.Align.OCFSpecBase as S
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionStageCore as F

hc-correspondence : ∀ (hc : HC (E.EBOψ 2)) → B.read F.reference ≅ treeᴴ hc
hc-correspondence hc = Lab-uniq F.reference-label (labᴴ hc)
hc-reference : HC (E.EBOψ 2) → Cd
hc-reference hc = B.forget (treeᴴ hc)
lightweight≤hc : ∀ hc → F.reference ≤ᵛ hc-reference hc
lightweight≤hc hc = ≤-trans (B.roundtrip≥ F.reference)
  (B.forget-mono (S.≅→≼ (hc-correspondence hc)))
hc≤lightweight : ∀ hc → hc-reference hc ≤ᵛ F.reference
hc≤lightweight hc = B.reference-lower-reflect (S.≅→≼ (≅-sym (hc-correspondence hc)))
lower-sound : ∀ hc {candidate : Cd} → F.reference ≤ᵛ candidate → treeᴴ hc V.≼ B.read candidate
lower-sound hc p = V.≼-trans (V.≅→≼ (≅-sym (hc-correspondence hc))) (Order.forward (B.read-mono p))
lower-reflect : ∀ hc {candidate : Cd} → treeᴴ hc V.≼ B.read candidate → F.reference ≤ᵛ candidate
lower-reflect hc p = B.read-reflect (Order.backward (V.≼-trans (V.≅→≼ (hc-correspondence hc)) p))

existing-HC-forward : F.reference ≤ᵛ hc-reference HC-BTBO
existing-HC-forward = lightweight≤hc HC-BTBO
existing-HC-backward : hc-reference HC-BTBO ≤ᵛ F.reference
existing-HC-backward = hc≤lightweight HC-BTBO
```

这不是未实例化的存在性记录：标签、整族、HC-BTBO及双向值桥都已给定。
普遍hc定理在逻辑上包含WfFsn的同项证书；直接写出其具体应用时的6G
编译尚未通过，因此不将该应用或与实际EBO-tree的分支连接计为已编译成果。
