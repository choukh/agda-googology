# normal1实际最高链的前缀动作解释

H仍保留真实model0前缀。桥证明原coordinate的全部分支与反馈，不重置种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputCoverModel where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
import OCF.Lean.BoundedDiagonalRel as D
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionFiniteValueIf as Actual
import OCF.Align.BoundedCompletionFiniteValueFirst as First
open import OCF.Align.BoundedCompletionTerminalRel using (terminal-rel)
open import OCF.Lean.FrozenWorldLift using (Same)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeValueFirst as V

U = step S⊥
prefix : HB U
prefix = Θ.model zero
H : HB U → HB U
H c = Old.act (prefix ⊞ c)

repeat-mixed : ∀ {a b : HB U} → Rel hz a b → ∀ n →
  Rel hz (Ops.partial U (λ _ → a) n) (mul b n)
repeat-mixed p zero = p
repeat-mixed p (suc n) = rel-add (repeat-mixed p n) p

native-act : ∀ {a b : HB U} → Rel hz a b → Rel hz
  (at 1 zero tt hself (hsuc hself) (up a)) (Old.act b)
native-act rz = rs rz
native-act (rs p) = rl (repeat-mixed (native-act p))
native-act (rl p) = rl (λ n → native-act (p n))
native-act (ro {κ = inj₁ ()} p)
native-act (ro {κ = inj₂ _} p) = ro (λ x y r → native-act (p x y r))

coordinate-rel : ∀ {a b : HB U} → Rel hz a b →
  Rel hz (Actual.coordinate zero a) (H b)
coordinate-rel rz = native-act (Θ.model-rel zero)
coordinate-rel (rs p) = rl (repeat-mixed (coordinate-rel p))
coordinate-rel (rl p) = rl (λ n → coordinate-rel (p n))
coordinate-rel (ro {κ = inj₁ ()} p)
coordinate-rel (ro {κ = inj₂ _} p) = ro (λ x y r → coordinate-rel (p x y r))

module Sim = D.Sim (Rel hz) (Rel hz)
  (Actual.coordinate zero) H (Actual.coordinate zero) H
  (rs rz) rel-add rel-add rl coordinate-rel coordinate-rel

model : HB U
model = diagonal H H
actual-model : Rel hz (Θ.normal 1) model
actual-model = subst (λ a → Rel hz a model)
  (Relation.Binary.PropositionalEquality.sym (First.normal-shape zero)) Sim.result

output : Cd
output = T.fold V.feedback model
actual-output : Same (T.fold V.feedback (Θ.normal 1)) output
actual-output = terminal-rel actual-model (pure-reflexive V.feedback)
```
