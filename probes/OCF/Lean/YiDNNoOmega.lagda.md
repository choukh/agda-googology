# NoΩ 偏移不能读到 slot
验收文件；编译否定：NoΩ 偏移与读回不低于 slot 的证据不能同时成立。
来源：直接应用 YiCNTw1.rdC-bound（无 Ω 形状层号的读法严格低于 Ω₁），未重证读回界。
不否定 SlotValue、实际深颈结点或含 Ω 形状的偏移；不提供矛盾前提下的 Law。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDNNoOmega where
open import Data.Empty using (⊥)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiNIDomain as D
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiCNTw1 as Bound
import OCF.Lean.YiVRRel as VR
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<; <ᵀ-asym)

Ω₁<slot : Bound.Ω₁ E.<ᵀ N.slot
Ω₁<slot = E.hd< (E.ar< E.[]<)

no-offset-slot : ∀ k → VR.NoΩ k → GR.Rd k N.slot → ⊥
no-offset-slot k no rd = <ᵀ-asym (Bound.rdC-bound k no rd) Ω₁<slot

no-offset-above-slot : ∀ k ν → VR.NoΩ k → N.slot ≤ᵀ ν → GR.Rd k ν → ⊥
no-offset-above-slot k ν no le rd = <ᵀ-asym (≤-< le (Bound.rdC-bound k no rd)) Ω₁<slot

slot-offset-notNoΩ : (d : D.Node) → GR.Rd (D.Node.offset d) N.slot
  → VR.NoΩ (D.Node.offset d) → ⊥
slot-offset-notNoΩ d rd no = no-offset-slot (D.Node.offset d) no rd
```
