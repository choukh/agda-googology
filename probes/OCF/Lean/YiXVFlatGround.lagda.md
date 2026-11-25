# YiXVFlatGround
> 验收文件。档位：编译定理。两有界目标层比较的完整零层实例，先于一般阶段实填。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFlatGround where
open import Data.Unit using (tt)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableGroundValue as G
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVFlatInput as Q
import OCF.Lean.YiXVRefLift as E
import OCF.Lean.YiXVRefAlgebra as R
bound : ∀ {a b} → Strong a → Strong b → (r : a L.<ᴵ b)
  (ρ : L.Simᴵ a b) (ξ : L.Simᴵ L.zero a) (ζ : L.Simᴵ L.zero b) (X : L.Ordᶜ L.zero) →
  A.Le (E.embedded ρ (Q.flat a ξ X)) (Q.flat b ζ X)
bound sa sb r ρ ξ ζ L.zero = E.embedded-Ω (L.<→◃ r) ρ
bound sa sb r ρ ξ ζ (L.suc X) = R.lim-mono (R.map-iter ρ (Q.good tt sa ξ (G.good X)) (bound sa sb r ρ ξ ζ X))
bound sa sb r ρ ξ ζ (L.lim f) = R.lim-mono (λ n → bound sa sb r ρ ξ ζ (f n))
bound sa sb r ρ ξ ζ (L.limᵢ () f)
bound sa sb r ρ ξ ζ (L.up () X)
ops : Q.Ops L.zero
Q.Ops.compare ops sa sb r ρ ξ ζ {X} gx = bound sa sb r ρ ξ ζ X
actual : A.Le (E.embedded (λ ()) (Q.flat L.zero (λ ()) (L.suc L.zero)))
  (Q.flat (L.suc L.zero) (λ ()) (L.suc L.zero))
actual = Q.Ops.compare ops tt tt L.zero (λ ()) (λ ()) (λ ()) A.groundΩ
```
