# 有界混合闭项的分量下界

先在同一签名比较所有分量，再通过已有公共上下文搬到同一目标。
无新占位前提；末尾直接实例化实际闭项的全部自然数分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedValueFloors where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.LHRecTy using (LH; Lv)
import OCF.Lean.BoundedContextTree as Tree
import OCF.Lean.BoundedContextClosed as Closed
import OCF.Align.ContextPullbackValue as V

right-add : ∀ {S} (a b : HB S) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))
right-add a (hΩ κ g) = Ω≤Ω (λ c → right-add a (g c))

module Floors (P k : LH) (w : Wd (Lv k)) (B : HB (Lv k)) where
  module M = Tree.Family P k w B
  module E = V.Value M.F M.T M.ctx

  floor≤sum : ∀ f n → M.floor (f n) ≤ᵛ M.sums f n
  floor≤sum f zero = ≤-refl _
  floor≤sum f (suc n) = right-add _ _
  floor≤mixed : ∀ f n → M.floor (f n) ≤ᵛ M.mixed f
  floor≤mixed f n = ≤l n (floor≤sum f n)
  relocated-floor≤output : ∀ f n → M.embed (M.floor (f n)) ≤ᵛ M.relocated f
  relocated-floor≤output f n = E.embed-mono (floor≤mixed f n)

open import OCF.Lean.LHRecLay using (ΩL)
module Actual = Floors (ΩL Closed.k) Closed.k Closed.w Closed.B

actual-component-lower : ∀ n → Closed.M.embed (Closed.M.floor (Closed.member n)) ≤ᵛ Closed.output
actual-component-lower = Actual.relocated-floor≤output Closed.member
```

这里下界是搬到公共目标后的原分量地板，不是新造的常值样本。
尚不能把它写成 ψ₀ 的下界：输入与输出都仍是高层树，没有在这里施行可数折叠。
