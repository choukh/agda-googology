# 旧第二地板覆盖全部有限最低 Ω 和

只用实际 Pure.ce、act 和末段 fold。有限 Ω 数不作为强度读法；
本篇先给整族真实闭项的值下界，记号校准在后篇。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformAcceptFamily where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure
open import OCF.Align.BoundedCompletionTerminalValueAct using (inflate)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.FrozenAbsorbSeed using (right-add)
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Lean.Fold1 as Original
import OCF.Align.BoundedNativeTerminalReady as T
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import Data.Unit using (tt)

stack : ℕ → HB U
stack zero = hz
stack (suc n) = stack n ⊞ floor
stack-self : ∀ n → VRel (stack n) (stack n)
stack-self zero = vz
stack-self (suc n) = add-rel (stack-self n) floor-self

floor≤coordinate : ∀ n → VRel floor (Old.Pure.ce n)
floor≤coordinate zero = floor-self
floor≤coordinate (suc n) = prefix-rel (floor≤coordinate n) _
stack≤coordinate : ∀ n → VRel (stack n) (Old.Pure.ce n)
stack≤coordinate zero = vz
stack≤coordinate (suc n) = add-rel (stack≤coordinate n) (inflate (floor≤coordinate n))

last : ∀ n → Old.Pure.oo n ≤ᵛ Old.Pure.oO n
last zero = ≤-refl _
last (suc n) = right-add (Old.Pure.oO n) (Old.Pure.oo (suc n))

family : ℕ → Cd
family n = T.fold hz (stack n)
family≤old2 : ∀ n → family n ≤ᵛ Original.TΩ (num 2) tt
family≤old2 n = ≤-trans (eval (stack≤coordinate n) (≤-refl hz))
  (≤-trans (last n) (≤-trans (≤l n (≤-refl _)) (same-value (same-sym Old.old2))))
whole≤old2 : hl family ≤ᵛ Original.TΩ (num 2) tt
whole≤old2 = l≤ family≤old2
```
