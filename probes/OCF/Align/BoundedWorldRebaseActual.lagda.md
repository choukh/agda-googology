# 原全部最高坐标及实际中槽的重定位实例

本文件不以手选单分量替换旧第三地板。输入直接为Whole原Col的全部
最高坐标，捕获槽既给出初始地板，也给出原Middle全部反馈坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseActual where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedCompletionUniformClosure using (floor-value)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Lean.TwoSlotValueClosure using (coordinate-self; coordinate-step; act-inflate)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Align.BoundedWorldValueTwoSlot using (U)
open import OCF.Align.BoundedWorldRebaseIf
open import OCF.Align.BoundedWorldRebaseRun
open import OCF.Align.BoundedWorldSeedClosure using (self0)
import OCF.Align.BoundedWorldSeedPrefix as Seed
import OCF.Align.BoundedWorldPrefixIf as Prefix
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedNativeValueFirst as First

encoded-self : ∀ n → Value (hs hz)
  (enc (floor zero) (Whole.Model.ce n)) (enc (floor zero) (Whole.Model.ce n))
encoded-self n = mono (coordinate-self n) (floor-value zero)

original≤encoded : ∀ n b → Value (hs hz) (Whole.Model.ce n) (enc b (Whole.Model.ce n))
original≤encoded n b = inflate (coordinate-self n) b

encoded-step : ∀ n → Value (hs hz)
  (enc (floor zero) (Whole.Model.ce n))
  (enc (act (floor zero)) (Whole.Model.ce (suc n)))
encoded-step n = mono (coordinate-step n) (act-inflate (floor-value zero))

slot : ℕ → ℕ → HB U
slot k n = Prefix.Middle.ce First.feedback (floor zero) (Whole.Model.ce k) n

all-feedback-self : ∀ k n j → Value (hs hz)
  (enc (slot k n) (Whole.Model.ce j)) (enc (slot k n) (Whole.Model.ce j))
all-feedback-self k n j = mono (coordinate-self j) (self0 (Seed.actual-coordinate k n))

all-feedback-lower : ∀ k n j → Value (hs hz)
  (Whole.Model.ce j) (enc (slot k n) (Whole.Model.ce j))
all-feedback-lower k n j = original≤encoded j (slot k n)
```

k=1是读取中槽的真实floor1加act floor1前缀，n遍历其所有回灌状态。
这些是编码的值关系，不是mid或low到Native的运行模拟；更不等于编码
树已合法或被C覆盖。所需的跨运行器模拟仍须单独证明。
