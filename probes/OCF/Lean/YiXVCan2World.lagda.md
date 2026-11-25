# YiXV: 实际孩子底的前提供给
> 验收文件。档位：编译定理。实际 E1 在每个参照 γ 2 n 上的目标 0 底界与目标 1 种子已实填；不声称整条外链上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2World where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (Ωt)
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold using (ns)
import OCF.Lean.YiXVThird as T
import OCF.Lean.YiXVSlotSrc as S
import OCF.Lean.YiXVCan2One as R1
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCan2SlotOne as Slot1
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVWorld3 as W
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Zero as Z
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCan2Gamma as G
import OCF.Lean.YiXVCan2Affine as A

floor : ∀ n → C.Le (G.Γ zero) (G.Γ n)
floor zero = C.Ω₂-refl
floor (suc n) = P.base (G.Γ n) (G.good (suc n))

module At (n : Data.Nat.ℕ) where
  module Actual = A.Affine I.D1 W.E1 (G.Γ n) (G.good n)
    (≼-trans W.b (Z.mono₀ (floor n))) (≼-trans W.s (Z.mono₀ (floor n)))
  first-upper : Actual.Both (suc zero) (L.suc O.Ω₁)
  first-upper = Actual.upper (O.gs O.Gd-Ω) (I.U.us I.zeroU) refl
  Ω-upper : Actual.Both (Ωt (suc zero)) (O.Ω₁ L.+ O.Ω₁)
  Ω-upper = Actual.upper (O.Gd-+ O.Gd-Ω O.Gd-Ω) I.ΩU H.Ω-closed
  seed : I.U.U T.η₁ (F.ψ₁ (G.Γ n))
  seed = I.U.uw (R1.good₁ C.Gd-Ω₂) S.actual-upper (R1.mono₁ (floor n))
  module Slot = Slot1.Fold I.D1 W.E1 (G.Γ n) (G.good n) T.η₁
    (ns T.B3 (suc zero) (ins (ins self))) seed S.actual-closed
  slot-Ω = Slot.result (O.Gd-+ O.Gd-Ω O.Gd-Ω) I.ΩU H.Ω-closed
```
