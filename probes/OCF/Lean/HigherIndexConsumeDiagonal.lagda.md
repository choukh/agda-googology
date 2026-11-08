# 阶段无关的完整纯参照覆盖

只要求新回调对每个实际Cd反馈覆盖旧纯动作；保留新链seed1与旧链seed0
的差异。用于任意经准入编码后变为纯Source后缀的实际Ω节点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeDiagonal where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.HigherIndexConsumePositive using (old-act; add-mono)
open import OCF.Lean.HigherIndexConsumeLowest using (oldF; old-compare)
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Old

module Cover (f : Cd → Cd) (action : ∀ d → old-act d ≤ᵛ f d) where
  module Original = F.Col _⊞_ _⊞_ (tt , hz) hz (λ W e → proj₁ W , e) oldF oldF
  coordinates : ∀ n → Original.ce n ≤ᵛ chain f n
  coordinates zero = z≤
  coordinates (suc n) = add-mono (coordinates n)
    (≤-trans (old-compare (Original.cw n) (coordinates n)) (action (chain f n)))
  outputs : ∀ n → Original.oo n ≤ᵛ f (chain f n)
  outputs n = ≤-trans (old-compare (Original.cw n) (coordinates n)) (action (chain f n))
  sums : ∀ n → Original.oO n ≤ᵛ Ops.partial S⊥ (λ j → f (chain f j)) n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
  whole : Old.TΩ1 ≤ᵛ diagonal f f
  whole = l≤ (λ n → ≤l n (sums n))
```

真实实例已有HigherIndexConsumeLowest；回调条件不是本闭项结论本身，
必须再由actual code及pure-suffix填入，才能用于原完整高层floor。
