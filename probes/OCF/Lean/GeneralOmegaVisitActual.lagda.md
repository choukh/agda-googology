# 全原采样、Λ累计阶段与真实分量嵌入的路径实例

实例只用原sample、ΣF和ι；没有将可入枝换成已访问样本，也不删除
累计前缀。本篇提供后续值验收可直接消费的真实路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaVisitActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (twL; ΛL)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.GeneralOmegaEmbedOmegaLayer using (tower-layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaFloorRun using (floor)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeRun using (coded)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeActual using (sum-right)
open import OCF.Lean.GeneralOmegaVisitIf
import OCF.Lean.GeneralOmegaSampleRun as S

node-sample : ∀ x κ f n → Visit (object x (S.Node.sample x κ f n)) (object x (hΩ κ f))
node-sample x κ f n = sampled n (here _)
lambda-stage : ∀ n → Visit (object ΛL (ΣF twL n)) (object ΛL (flL ΛL))
lambda-stage n = natural n (here _)
tower-component : ∀ n → Visit (object (twL n) (flL (twL n)))
  (object ΛL (ι n (flL (twL n))))
tower-component n = embedded (sum-right (coded (tower-layer n) (floor (tower-layer n)))) (here _)
```

tower-component的终点是原单分量，不是原累计ΣF。把这个值送到某个
实际ΣF/θ回调，仍需保留前缀的另一步值定理，不能由此实例免费推出。
