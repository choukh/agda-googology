# 实际 EBO 参照在 Cd 上的验收入口

本篇只定义验收参照，不是记号无关的候选。参照来自 WfFsn 的实际
EBO-tree；所有定义与结论留在验收侧。用 opaque 避免消费者为了比较
类型而展开沿良基证明生成的大树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaCountableTarget where

open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
import OCF.Align.WfFsn as E
import OCF.Align.Value as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.LambdaOrderBridge as R

opaque
  reference : Cd
  reference = B.forget E.EBO-tree

  lower-sound : ∀ {candidate : Cd} → reference ≤ᵛ candidate →
    E.EBO-tree V.≼ B.read candidate
  lower-sound {candidate} p = R.forward
    (B.reference-lower {r = E.EBO-tree} {a = candidate} p)

  lower-reflect : ∀ {candidate : Cd} → E.EBO-tree V.≼ B.read candidate →
    reference ≤ᵛ candidate
  lower-reflect {candidate} p = B.reference-lower-reflect
    {r = E.EBO-tree} {a = candidate} (R.backward p)

reference-instance : reference ≤ᵛ reference
reference-instance = ≤-refl reference
```

因此对独立 Cd 候选证明 reference≤ᵛcandidate，精确对应终点要求的
EBO 下界，不是以不同参照替代目标。自身实例只验证验收条件非空，
reference 读记号，不能进入最终定义或其证书。这里没有构造成品候选。

编译需归档的临时拷贝，路径与库设置同 WfFsn；编译状态记录在 LOG。
