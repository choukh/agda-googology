# 同类型全保留动作的树值膨胀

这是原self-target计算方程将要使用的统一值引理。不从源类型宽度推出强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueAffine where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤l; l≤; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)
import OCF.Lean.BoundedMixedAffine as A

right-add : ∀ {S} (a b : HB S) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))
right-add a (hΩ κ g) = Ω≤Ω (λ e → right-add a (g e))

module Affine (S : KS) where
  module Action = A.Action S (hs hz)
  positive : ∀ a → hs hz ≤ᵛ Action.run a
  positive hz = s≤s z≤
  positive (hs a) = ≤l 0 (positive a)
  positive (hl f) = ≤l 0 (positive (f 0))
  positive (hΩ κ g) = ≤Ω (bot S κ) (positive (g (bot S κ)))

  inflation : ∀ a → a ≤ᵛ Action.run a
  inflation hz = z≤
  inflation (hs a) = ≤l 1 (≤-trans (s≤s (inflation a))
    (⊞-≤ʳ (Action.run a) (positive a)))
  inflation (hl f) = l≤ (λ n → ≤l n (inflation (f n)))
  inflation (hΩ κ g) = Ω≤Ω (λ e → inflation (g e))
```

positive与inflation对整个KS参数统一，原动作本身已有定义，未新增运行器。
本篇单独不是FirstFloor实例；尚须将真实coordinate的计算接到该动作。
