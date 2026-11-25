# 首个正单位的一级槽与旧链第三前缀

> 第四层，无条件。从指定实际槽的读值任取有限次 ε⁺，全列上确界仍严格小于旧链第三前缀 ψ₀(Ω₃)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LegacySlot where
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import WVOne using (T₀)
import W4Block as W
import B12BtboCut as C
import Survey.W4FiniteOmegaCut as Finite
import B31UStage as Slot
import B23NDomain as Domain
import B12Omega3Ref as Ref₃
import B22MovingIndex as Eps
import Survey.W4PTOFinite as Calibration
import Survey.W4LegacyOmega as Old
open import OCF.Lean.YiRefTw2 using (Rt)
import Survey.EboPTOFinite as Code
open import Data.Empty using (⊥)

module Block = Finite.Branch 1 2
module Named (k : ℕ) where
  actual = Ref₃.at (C.finite 3) k
  named = Rt (Code.tower-h 2 (suc k))
  to-name : actual ≼ named
  to-name = proj₂ (Calibration.id₂-branch k)
  from-name : named ≼ actual
  from-name = proj₁ (Calibration.id₂-branch k)

  through-child : ∀ (j : ℕ) (x : T₀) → x ≼ Ref₃.at actual j → x ≼ named
  through-child j x h = ≼-trans {a = x} {b = actual} {c = named}
    (≼-trans {a = x} {b = Ref₃.at actual j} {c = actual} h (Ref₃.at-below actual j)) to-name

module From (receipt : T₀) (slot-value : receipt ≼ Domain.child) where
  scalar-limit : T₀
  scalar-limit = L.lim (W.iter Eps.above receipt)

  slot-start : receipt ≼ Rt Block.root
  slot-start = Named.through-child 2 0 receipt slot-value

  slot-ceiling : scalar-limit ≼ Ref₃.at (C.finite 3) 3
  slot-ceiling = ≼-trans {a = scalar-limit} {b = Rt Block.ceiling} {c = Named.actual 3}
    (Block.all receipt slot-start) (Named.from-name 3)

  slot-gap : L.suc scalar-limit ≼ Old.p 2
  slot-gap = ≼-trans {a = L.suc scalar-limit} {b = L.suc (Rt Block.ceiling)} {c = Old.p 2}
    (s≼s {a = scalar-limit} {b = Rt Block.ceiling} (Block.all receipt slot-start))
    (≼-trans {a = L.suc (Rt Block.ceiling)} {b = C.finite 3} {c = Old.p 2} Block.proper (proj₁ Old.third))

  no-transfer-from-slot : Old.p 2 ≼ scalar-limit → ⊥
  no-transfer-from-slot h = s≼-irrefl scalar-limit (≼-trans {a = L.suc scalar-limit} {b = Old.p 2} {c = scalar-limit} slot-gap h)

module Actual = From _ Slot.actual
```
