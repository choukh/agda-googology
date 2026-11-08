# 原反馈链的层索引关系模拟

中间层的逻辑关系可以比全Same弱，只有最终可数层再推出Same或值界。
本篇对任意坐标关系R、输出关系Q直接模拟原chain/diagonal，保留全部
实际回灌项；不从相同坐标的逐点关系推出异坐标的回调相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedDiagonalRel where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)

module Sim {S T : KS}
  (R : HB S → HB S → Set) (Q : HB T → HB T → Set)
  (f f′ : HB S → HB S) (g g′ : HB S → HB T)
  (start : R (hs hz) (hs hz))
  (addR : ∀ {a b c d} → R a b → R c d → R (a ⊞ c) (b ⊞ d))
  (addQ : ∀ {a b c d} → Q a b → Q c d → Q (a ⊞ c) (b ⊞ d))
  (limQ : ∀ {a b : ℕ → HB T} → (∀ n → Q (a n) (b n)) → Q (hl a) (hl b))
  (step : ∀ {a b} → R a b → R (f a) (f′ b))
  (emit : ∀ {a b} → R a b → Q (g a) (g′ b)) where

  coordinates : ∀ n → R (chain f n) (chain f′ n)
  coordinates zero = start
  coordinates (suc n) = addR (coordinates n) (step (coordinates n))

  outputs : ∀ n → Q (g (chain f n)) (g′ (chain f′ n))
  outputs n = emit (coordinates n)

  partials : ∀ n → Q
    (Ops.partial T (λ k → g (chain f k)) n)
    (Ops.partial T (λ k → g′ (chain f′ k)) n)
  partials zero = outputs zero
  partials (suc n) = addQ (partials n) (outputs (suc n))

  result : Q (diagonal f g) (diagonal f′ g′)
  result = limQ partials

open import OCF.Lean.FrozenWorldLift using (Same; ss; zz; ll)
import OCF.Lean.BoundedDiagonalSame as SameTool

module Example (S : KS) = Sim {S} {step S} Same Same
  (λ a → a) (λ a → a) up up
  (ss zz) SameTool.same-add SameTool.same-add (λ p → ll p)
  (λ p → p) SameTool.up-same
```

Example提供非恒定回调的实际实例，前提不是空的。Sim本身不要求R/Q
自反于全部raw树，不要求它们判定相等或比较下标；若取受限逻辑关系，
每次回调均必须交付该关系的真实证据。它也不是原fold已保持某关系的
结论；该结论必须由消费者对实际分支递归证明。
