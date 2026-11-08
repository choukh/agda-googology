# 同上下文保留实验的树值下界

比较同一目标中的纯搬运树与实验输出：纯搬运保0/后继，实验将0送1、
后继送重复和。全部Ω种类及坐标使用相同Ctx，所以值比较可以统一归纳。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCtxValue where
open import Data.Nat using (zero)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (ek; frC)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeCtxIf using (context)
import OCF.Align.BoundedNativeCtxRun as Run
import OCF.Align.BoundedNativeCtxSelect as Select
import OCF.Align.BoundedNativeViewNegOutput as Old
open import OCF.Align.BoundedNativeViewNegCopies using (pc)

add-mono : ∀ {S} {a b c d : HB S} → a ≤ᵛ b → c ≤ᵛ d → (a ⊞ c) ≤ᵛ (b ⊞ d)
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)

module Value {c t : Cd} (q : c ⊲ t) where
  module K = Run.Keep q
  C = context q

  embed : HB (Native c) → HB (Native t)
  embed hz = hz
  embed (hs a) = hs (embed a)
  embed (hl f) = hl (λ n → embed (f n))
  embed (hΩ κ g) = hΩ (ek C κ) (λ e → embed (g (frC C κ e)))

  positive : ∀ a → hs hz ≤ᵛ K.run a
  positive hz = s≤s z≤
  positive (hs a) = ≤l 0 (positive a)
  positive (hl f) = ≤l 0 (positive (f 0))
  positive (hΩ κ g) = ≤Ω (bot (Native t) (ek C κ))
    (positive (g (frC C κ (bot (Native t) (ek C κ)))))

  lower : ∀ a → embed a ≤ᵛ K.run a
  lower hz = z≤
  lower (hs a) = ≤l 1 (add-mono (lower a) (positive a))
  lower (hl f) = l≤ (λ n → ≤l n (lower (f n)))
  lower (hΩ κ g) = Ω≤Ω (λ e → lower (g (frC C κ e)))

module Actual = Value pc

actual-lower : Actual.embed Old.floor ≤ᵛ Select.output
actual-lower = Actual.lower Old.floor
```

actual-lower给已证合法的Select.output一个确切目标树下界，未把合法
修复实验当作已经达到某个ψ₀。纯搬运树、实验及原错误输出之间的
其它值比较仍须单独证明；本文没有宣称原运行器的整体修复已完成。
