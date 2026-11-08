# 真实前缀下的零规则比较

把上一轮1与Ω的采样比较推广到实际旧轨道的全部前缀：后继折叠
被加一个最低 Ω 的动态折叠覆盖。证明明确使用第一个反馈坐标，
不声称末段折叠保任意高层值序，也不假设加法同态。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperPrefix where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l; z≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; mul-≤)
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-mul)
open import OCF.Align.FrozenAbsorbSeed using (right-add)
open import OCF.Align.BoundedCompletionTerminalValueIf using (VRel; U)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (floor; seed-mono; terminal-prefix)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
open import OCF.Align.BoundedCompletionTerminalValueAct using (old-coordinate-self)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.FrozenAbsorbNegUpper as P

fold-tail : ∀ b (a : HB U) c → Same (T.fold b (a ⊞ up c)) (P.P (T.fold b a) c)
fold-tail b a hz = same-refl _
fold-tail b a (hs c) = ll (same-mul (fold-tail b a c))
fold-tail b a (hl f) = ll (λ n → fold-tail b a (f n))

module Prefix (b : HB U) (bb : VRel b b) (v : Cd) where
  module Orbit = T.Orbit v (λ c → b ⊞ up c)
  B : Cd
  B = T.fold v b
  base≤output0 : B ≤ᵛ Orbit.C.oo zero
  base≤output0 = terminal-prefix bb (up v) v
  initial≤next : v ≤ᵛ Orbit.C.ce 1
  initial≤next = ≤⊞ _ _
  positive-next : hs hz ≤ᵛ Orbit.C.ce 1
  positive-next = ≤-trans (terminal-positive v (b ⊞ up v)) (right-add v (Orbit.C.oo zero))

  repeated≤output1 : hl (mul B) ≤ᵛ Orbit.C.oo 1
  repeated≤output1 = ≤-trans
    (P.mono (seed-mono bb initial≤next) positive-next)
    (same-value (same-sym (fold-tail (Orbit.C.ce 1) b (Orbit.C.ce 1))))
  repeated≤whole : hl (mul B) ≤ᵛ T.fold v (b ⊞ floor)
  repeated≤whole = ≤l 1 (≤-trans repeated≤output1 (right-add (Orbit.C.oo zero) (Orbit.C.oo 1)))

prefix-step : ∀ {a b : HB U} → VRel a b → VRel b b → ∀ {u v} → u ≤ᵛ v →
  T.fold u (hs a) ≤ᵛ T.fold v (b ⊞ floor)
prefix-step {b = b} ab bb {v = v} uv = ≤-trans
  (l≤ (λ n → ≤l n (mul-≤ (eval ab uv) n))) (Prefix.repeated≤whole b bb v)

actual-coordinate-step : ∀ n {u v} → u ≤ᵛ v →
  T.fold u (hs (Old.Pure.ce n)) ≤ᵛ T.fold v (Old.Pure.ce n ⊞ floor)
actual-coordinate-step n uv = prefix-step (old-coordinate-self n) (old-coordinate-self n) uv
```

最后的定理覆盖原 Pure.ce 全轨道、任意有序种子；前提实例由已有
old-coordinate-self逐轨道提供。它是上界模拟的一步闭包，不是Old2
具名上界：仍需把这些步进组织成统一的跨输入/跨坐标模拟并接参照。
