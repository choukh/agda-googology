# 所有可数层共用的实际链补偿预算

把最低层2n+3预算改写成任意c的同一定理。关系采用有证采样Value，
传递来自其已证compose；H只需保自证、膨胀、恒正，不要求H单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseBudget where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′; m≤n⇒m≤1+n)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Lean.RebaseLayerIf
open import OCF.Lean.RebaseLayerClosure using (compose; prefix; add; positive; act-mono)
open import OCF.Lean.GeneralRebaseSampleRun using (right)

pad : ∀ {S} → (ℕ → HB S) → ℕ → HB S
pad f zero = f zero
pad f (suc n) = pad f n ⊞ hs (f (suc n))
budget : ℕ → ℕ
budget zero = 3
budget (suc n) = suc (suc (budget n))
small≤budget : ∀ n → suc (suc (suc n)) ≤ budget n
small≤budget zero = s≤s (s≤s (s≤s z≤n))
small≤budget (suc n) = s≤s (m≤n⇒m≤1+n (small≤budget n))

module Cover (c : Cd) (H : HB (Native c) → HB (Native c))
  (keeps : ∀ e → Value c e e → Value c (H e) (H e))
  (inflates : ∀ e → Value c e e → Value c e (H e))
  (positive-H : ∀ e → Value c e e → Value c (hs hz) (H e)) where
  trans = compose c
  selves : ∀ n → Value c (chain H n) (chain H n)
  selves zero = vs vz
  selves (suc n) = add (selves n) (keeps _ (selves n))
  output-selves : ∀ n → Value c (H (chain H n)) (H (chain H n))
  output-selves n = keeps _ (selves n)
  chain-step : ∀ n → Value c (chain H n) (chain H (suc n))
  chain-step n = prefix (selves n) _
  steps : ∀ {j n} → j ≤′ n → Value c (chain H j) (chain H n)
  steps {j} ≤′-refl = selves j
  steps (≤′-step {n = n} p) = trans (steps p) (chain-step n)
  indexed : ∀ {j n} → j ≤ n → Value c (chain H j) (chain H n)
  indexed p = steps (≤⇒≤′ p)

  samples : ℕ → HB (Native c)
  samples n = H (chain H (suc n))
  next-bound : ∀ n → Value c (samples (suc n)) (chain H (budget n))
  next-bound n = trans
    (right (chain H (suc (suc n))) (output-selves (suc (suc n))))
    (indexed (small≤budget n))
  padded : ∀ n → Value c (pad samples n) (chain H (budget n))
  padded zero = trans (right (chain H 1) (output-selves 1)) (chain-step 2)
  padded (suc n) = trans (vs (add (padded n) (next-bound n)))
    (trans
      (vs (add (selves (budget n)) (inflates _ (selves (budget n)))))
      (add (selves (suc (budget n))) (positive-H _ (selves (suc (budget n))))))
  last : ∀ n → Value c (H (chain H n))
    (Ops.partial (Native c) (λ j → H (chain H j)) n)
  last zero = output-selves zero
  last (suc n) = right (Ops.partial (Native c) (λ j → H (chain H j)) n)
    (output-selves (suc n))
  padded-partial : ∀ n → Value c (pad samples n)
    (Ops.partial (Native c) (λ j → H (chain H j)) (budget n))
  padded-partial n = trans (padded n)
    (trans (inflates _ (selves (budget n))) (last (budget n)))

act-inflate : ∀ {S A Q a b} → SampleValue S A Q a b →
  SampleValue S A Q a (act b)
act-inflate vz = vz
act-inflate {b = hs b} (vs p) = vli 1 (add (act-inflate p) (positive b))
act-inflate (vr p) = vli 0 (act-inflate p)
act-inflate (vl p) = vl (λ n → act-inflate (p n))
act-inflate (vli n p) = vli n (act-inflate p)
act-inflate (vo p) = vo (λ x y xy → act-inflate (p x y xy))
act-inflate (vor p) = vor (λ e se → act-inflate (p e se))

module Actual (c : Cd) = Cover c act
  (λ e se → act-mono se) (λ e se → act-inflate se) (λ e se → positive e)
```

Actual对每个c提供原act的非零实例，不是空接口。padded-partial目标是
原Ops.partial与原chain；并未改运行器或阶段输出。此关系预算若要给
高层实际fold的值界，仍须证明该fold保持有证采样关系及其实际采样自证。
