# 前缀模拟在原第三地板全坐标族上的实例

p_k逐字取旧最高回灌坐标，不另造prefix文法。中槽从floor0变化到
act floor0；底槽取真实非零feedback。结论覆盖各中Ω的全部输出部分和。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldPrefixActual where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionUniformClosure using (floor-value)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Lean.TwoSlotValueClosure using (coordinate-step; act-inflate)
open import OCF.Align.BoundedWorldPrefixIf
import OCF.Align.BoundedWorldPrefixRun as Run
import OCF.Align.BoundedWorldPrefixSeed as Seed
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedNativeValueFirst as First

actual-prefix : Whole.Model.ce 1 ≡ Seed.prefix
actual-prefix = refl

all-sums : ∀ k {u v} → u ≤ᵛ v → ∀ n →
  Middle.oO u (floor zero) (Whole.Model.ce k) n ≤ᵛ
  Middle.oO v (act (floor zero)) (Whole.Model.ce (suc k)) n
all-sums k uv = Run.Compare.sums uv (act-inflate (floor-value zero)) (coordinate-step k)

all-whole : ∀ k {u v} → u ≤ᵛ v →
  hl (Middle.oO u (floor zero) (Whole.Model.ce k)) ≤ᵛ
  hl (Middle.oO v (act (floor zero)) (Whole.Model.ce (suc k)))
all-whole k uv = Run.whole uv (act-inflate (floor-value zero)) (coordinate-step k)

nonzero-prefix-sums : ∀ n →
  Middle.oO First.feedback (floor zero) Seed.prefix n ≤ᵛ
  Middle.oO First.feedback (act (floor zero)) (Whole.Model.ce 2) n
nonzero-prefix-sums = all-sums 1 (≤-refl First.feedback)

nonzero-prefix-whole :
  hl (Middle.oO First.feedback (floor zero) Seed.prefix) ≤ᵛ
  hl (Middle.oO First.feedback (act (floor zero)) (Whole.Model.ce 2))
nonzero-prefix-whole = all-whole 1 (≤-refl First.feedback)
```

这是有真实非零prefix与底槽的完整中Ω模拟，不是Old2首项；右侧仍有
动态中槽。因此它不等于Old3≤C。剩余需要把右侧变动中槽及输入前缀
同时送入实际Uniform/normal，不能只用最高坐标的stride关系。
