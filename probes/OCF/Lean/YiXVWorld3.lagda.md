# YiXV：含 pre 1 的实际孩子底
> 验收文件。编译定理：B3 的实际孩子底 E1 满足带前缀上界保持的两个前提，world-upper 在 U/Closed/Good 域上成立。
> 底分量分别用 YiXVTwo.pre1-upper 与 YiXVThirdZero.actual-upper，first-upper/Ω-upper 是该底上的闭实例。
> 未给所有内链项新的 U 证据，未证明 pre 2、Need1 或全塔的上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVWorld3 where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVThird as T
import OCF.Lean.YiXVThirdZero as Z
import OCF.Lean.YiXVTwo as W
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVAffine as P

E2 : Base (suc (suc zero))
E2 = dS (suc (suc zero)) tt tt T.B3 zero
E1 : Base (suc zero)
E1 = dS (suc zero) tt tt E2 zero

b : read (b⊥ E1) ≼ L.ψ⁰ F.Ω₂
b = W.pre1-upper
s : read (bs E1 zero (ins self)) ≼ L.ψ⁰ F.Ω₂
s = Z.actual-upper

module Actual = P.Affine I.D1 E1 F.Ω₂ F.Ω₂-refl b s

world-upper : ∀ {y Y} → O.Gd Y → (h : S.Sim.U I.D1 y Y) → H.Anchor.Closed I.D1 h → Actual.Both y Y
world-upper = Actual.upper

first-upper : Actual.Both (suc zero) (L.suc O.Ω₁)
first-upper = world-upper (O.gs O.Gd-Ω) (I.U.us I.zeroU) refl

Ω-upper : Actual.Both (Ωt (suc zero)) (O.Ω₁ L.+ O.Ω₁)
Ω-upper = world-upper (O.Gd-+ O.Gd-Ω O.Gd-Ω) I.ΩU H.Ω-closed
```
