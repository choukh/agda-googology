# 首轮中间值在实际正槽 (0,1) 上的检验

第四层，无条件。该槽完整零层返回严格低于 ψ₀(Ω_ω)。有限层的上界取自第 31 批。[初段与门槛](W4Rule48.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4Rule48Slot where

open import OCF.Align.Value using (_≼_; s≼s; ≼-trans)
import OCF.Align.Level as L
import B12BtboCut as Cut
import B23NDomain as G
import B31UStage as Slot
import B31UStageReference as Bound
import Survey.W4Rule48 as Probe

import B12Terminal as T
import WVTwo as V
import B31UFirst as U
import B31UStageOp as Op
import B31PCell as Cell
open import Relation.Binary.PropositionalEquality using (_≡_)

module At (r : T.Run V.lvl2) where
  module Q = Slot.Take r
  module Receive (eq : Q.Z.Run.c ≡ Op.subject) where
    module R = Q.Receive eq
    cap : Q.Paid → Q.Z.receipt ≼ Cut.finite 3
    cap ticket = ≼-trans {a = Q.Z.receipt} {b = G.child} {c = Cut.finite 3}
      (R.close ticket) Bound.three

    short : Q.Paid → L.suc Q.Z.receipt ≼ Probe.Start.H.middle
    short ticket = ≼-trans {a = L.suc Q.Z.receipt} {b = L.suc (Cut.finite 3)} {c = Probe.Start.H.middle}
      (s≼s {a = Q.Z.receipt} {b = Cut.finite 3} (cap ticket)) Probe.finite-three-short

module Actual = At.Receive (U.Actual.state 0 1) Cell.positive
slot-short = Actual.short Slot.ticket
```
