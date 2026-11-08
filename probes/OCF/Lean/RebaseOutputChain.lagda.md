# 实际反馈链吸收输出补偿，不要求动作单调

若H保持Seed0、膨胀且恒正，则第n个带后继补偿的输出和进入原链
第2n+3点。这里只用已经访问的实际链点，无须反演H的单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseOutputChain where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′; m≤n⇒m≤1+n)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; right-rel)
open import OCF.Align.BoundedWorldValueTwoSlot using (U)
open import OCF.Align.BoundedWorldSeedIf using (Seed0)
open import OCF.Align.BoundedWorldSeedClosure using (self0)
open import OCF.Align.BoundedWorldSeedCompose using (trans0)
open import OCF.Lean.RebaseMiddleRun using (one-seed; chain-seed)
import OCF.Align.BoundedCompletionOutputPadding as P

budget : ℕ → ℕ
budget zero = 3
budget (suc n) = suc (suc (budget n))
small≤budget : ∀ n → suc (suc (suc n)) ≤ budget n
small≤budget zero = s≤s (s≤s (s≤s z≤n))
small≤budget (suc n) = s≤s (m≤n⇒m≤1+n (small≤budget n))

module Cover (H : HB U → HB U)
  (keeps : ∀ e → Seed0 e → Seed0 (H e))
  (inflates : ∀ e → Seed0 e → Value hz e (H e))
  (positive : ∀ e → Seed0 e → Value hz (hs hz) (H e)) where

  seeds : ∀ n → Seed0 (chain H n)
  seeds = chain-seed H keeps
  selves : ∀ n → Value hz (chain H n) (chain H n)
  selves n = self0 (seeds n)
  output-selves : ∀ n → Value hz (H (chain H n)) (H (chain H n))
  output-selves n = self0 (keeps _ (seeds n))
  chain-step : ∀ n → Value hz (chain H n) (chain H (suc n))
  chain-step n = prefix-rel (selves n) _
  steps : ∀ {j n} → j ≤′ n → Value hz (chain H j) (chain H n)
  steps {j} ≤′-refl = selves j
  steps (≤′-step {n = n} p) = trans0 (steps p) (chain-step n)
  indexed : ∀ {j n} → j ≤ n → Value hz (chain H j) (chain H n)
  indexed p = steps (≤⇒≤′ p)

  samples : ℕ → HB U
  samples n = H (chain H (suc n))
  next-bound : ∀ n → Value hz (samples (suc n)) (chain H (budget n))
  next-bound n = trans0
    (right-rel (chain H (suc (suc n))) (output-selves (suc (suc n))))
    (indexed (small≤budget n))

  padded : ∀ n → Value hz (P.pad samples n) (chain H (budget n))
  padded zero = trans0 (right-rel (chain H 1) (output-selves 1)) (chain-step 2)
  padded (suc n) = trans0 (vs (add-rel (padded n) (next-bound n)))
    (trans0
      (vs (add-rel (selves (budget n)) (inflates _ (seeds (budget n)))))
      (add-rel (selves (suc (budget n))) (positive _ (seeds (suc (budget n))))))

  last : ∀ n → Value hz (H (chain H n)) (Ops.partial U (λ j → H (chain H j)) n)
  last zero = output-selves zero
  last (suc n) = right-rel (Ops.partial U (λ j → H (chain H j)) n) (output-selves (suc n))

  padded-partial : ∀ n → Value hz (P.pad samples n)
    (Ops.partial U (λ j → H (chain H j)) (budget n))
  padded-partial n = trans0 (padded n)
    (trans0 (inflates _ (seeds (budget n))) (last (budget n)))
```

给非空实际实例，避免将条件接口本身当可用定理。

```agda
open import OCF.Align.BoundedWorldCoverIf using (act)
import OCF.Align.BoundedWorldSeedClosure as S
import OCF.Lean.TwoSlotValueClosure as A
module Actual = Cover act (λ e se → S.act0 se)
  (λ e se → A.act-inflate (self0 se)) (λ e se → A.act-positive hz e)
```

实际重定位分支H的三个字段另由跨运行器定理提供。padded-partial的
目标仍是原Ops.partial，不是另造有界模型；本篇尚不替代low输出比较。
