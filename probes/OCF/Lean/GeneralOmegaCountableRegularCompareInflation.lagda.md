# 原Γ的高度膨胀与全部实际迭代增长

后继利用原完整无累加反馈列，极限利用每个原分量的规范捕获。
该归纳比较输入高度与其实际输出，不比较两个任意高度上的Γ值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareInflation where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; stage; positive)
open import OCF.Lean.GeneralOmegaCountableSuccessorRun using (whole)
import OCF.Lean.GeneralOmegaCountableSuccessorIf as I
open import OCF.Lean.GeneralOmegaCountableRegularCompareCanonical using (collapse; canonical-component)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)

module Successor (B : Cd) (lB : LgB B) where
  module S = I.At B lB
  positive-next : hs hz ≤ᵛ leg (S.read-orbit 1)
  positive-next = ≤-trans (positive B lB (z⊲ᴮ B) (S.P.NoSum 1))
    (inflation (S.read-orbit 1))
  first-two : hs (collapse B lB) ≤ᵛ leg (hl S.read-orbit)
  first-two = ≤l 1 (⊞-≤ʳ (collapse B lB) positive-next)
  strict : hs (collapse B lB) ≤ᵛ collapse (hs B) lB
  strict = ≤-trans first-two (same-value (same-sym (leg-same (whole B lB))))

collapse-height-inflation : ∀ B lB → B ≤ᵛ collapse B lB
collapse-height-inflation hz lB = z≤
collapse-height-inflation (hs B) lB = ≤-trans
  (s≤s (collapse-height-inflation B lB)) (Successor.strict B lB)
collapse-height-inflation (hl f) lB = l≤ (λ n → ≤-trans
  (collapse-height-inflation (f n) (proj₂ lB n)) (canonical-component f lB n))
collapse-height-inflation (hΩ () f) lB
Γ-inflation : ∀ c → c ≤ᵛ Γ c
Γ-inflation c = ≤-trans (inflation c) (collapse-height-inflation (leg c) (Lg-leg c))
stage-growth : ∀ n → stage n ≤ᵛ stage (suc n)
stage-growth n = Γ-inflation (stage n)
```

这证明原闭项实际迭代的全部弱增长。Successor.strict针对规范
collapse的输入后继；Γ-inflation仅比较c与Γc，没有将任意c≤d
送过Γ，也未声称Γc至少为hs c或此迭代已达到ψ₀Λ。
