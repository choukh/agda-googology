# 全部原可数高度的typed逐点观察实现

验收专用。这里将实际分类节点实例填入Read递归，所得根结论不再
带未填Nodes。参照层是原合法B的同形height B，不把它等同于另一个
未完成输入的toLevel层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveActual where
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read)
open import OCF.Align.GeneralOmegaCountableTypedValueObserveIf
open import OCF.Align.GeneralOmegaCountableTypedValueObserveRecursor
open import OCF.Align.GeneralOmegaCountableTypedValueObserveNode using (instance-nodes)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z

module Actual = Build instance-nodes
instance-full : FullObservation
FullObservation.internal instance-full B lB t ht r = Result.internal (Actual.build r) t ht
FullObservation.root instance-full B lB r = Result.root (Actual.build r) (z⊲ᴮ B)
instance-root : RootObservation
RootObservation.preserve instance-root B lB r = FullObservation.root instance-full B lB r

floor-observation : ∀ B lB pt → L.ψ⁰ (L.Ω (height B lB)) L.≅
  Z.read (point-observe B lB hz pt (pointFloor B))
floor-observation B lB pt = Result.root (Actual.build (floor-read B lB)) pt
omega-instance : L.ψ⁰ (L.Ω (height omega omega-legal)) L.≅
  Z.read (point-observe omega omega-legal hz (z⊲ᴮ omega) (pointFloor omega))
omega-instance = floor-observation omega omega-legal (z⊲ᴮ omega)
```

all-B字段包含所有反馈坐标及实际非有限ω，不只是最高节点样本。
该接口不提供跨不同B的值单调，也没有把γ₁的旧层搬到双完成高度。
