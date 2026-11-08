# 全有限候选的已验收第二站

验收专用。本篇给原全有限闭项的真实非空具名下界，未将第二站
冒称全有限族验收；输入、反馈和完成全部使用原Closed定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedAllActual where
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Lean.GeneralOmegaFiniteObserveClosed as C
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaCoverFinite as F
open import OCF.Align.GeneralOmegaFiniteTypedAllSecond using (whole)

reference≤second : F.finite 2 ≤ᵛ C.stage 2
reference≤second = B.reference-lower-reflect (V.≅→≼ whole)
second≤reference : C.stage 2 ≤ᵛ F.finite 2
second≤reference = ≤-trans (B.roundtrip≥ (C.stage 2))
  (B.forget-mono (V.≅→≼ (L.≅-sym whole)))
reference≤tree : F.finite 2 ≤ᵛ C.tree
reference≤tree = ≤-trans reference≤second (C.stage-lower 2)
```

原stage2与ψ₀(Ω₂)参照互相≤ᵛ，合法tree得到此下界。全n的桥尚缺
原有限层嵌入路径与目标路径共同保留的Read模拟；up的输入层下降
不能当成观察目标也下降。这里没有假定任意函数吃Same，也没有把
高层位置或值关系无条件搬过观察器。γ₂首回调的整族覆盖仍待证明。
