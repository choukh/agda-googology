# 原第三地板全部输出的实际低比较

以下直接实例化原Whole最高反馈坐标，输入和中槽证书均有已编译实例。
不是只取首项，也没有把目标定义为旧输出自身。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseLowActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionUniformClosure using (floor-value)
open import OCF.Lean.TwoSlotValueClosure using (coordinate-self)
open import OCF.Align.BoundedWorldSeedActual using (old1-coordinates)
import OCF.Align.BoundedWorldSeedClosure as S
open import OCF.Align.BoundedWorldValueTwoSlot using (low)
open import OCF.Lean.RebaseMiddleIf using (eval)
open import OCF.Align.BoundedWorldRebaseLowRun using (lower)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedWorldValueWhole as Whole

outputs : ∀ n → low hz (floor zero) (Whole.Model.ce n) ≤ᵛ
  T.fold hz (eval (floor zero) (Whole.Model.ce n))
outputs n = lower S.floor0 S.floor0 (old1-coordinates n) (old1-coordinates n)
  (coordinate-self n) (floor-value zero) z≤

sums : ∀ n → Whole.Model.oO n ≤ᵛ
  Σ₀ (λ j → T.fold hz (eval (floor zero) (Whole.Model.ce j))) n
sums zero = outputs zero
sums (suc n) = add-mono (sums n) (outputs (suc n))

whole : Whole.output ≤ᵛ
  hl (Σ₀ (λ j → T.fold hz (eval (floor zero) (Whole.Model.ce j))))
whole = l≤ (λ n → ≤l n (sums n))
```

这里目标尚为raw输出和；合法完成与旧TΩ3的结构桥由独立模块连接。
不预设此树的具名强度，也不声称它被C覆盖。
