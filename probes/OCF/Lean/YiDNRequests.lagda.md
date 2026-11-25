# slot 成员的偏移读回前提
验收文件；编译定理：偏移读回给出请求，指定成员的 index 逐字为 slot。
SlotLaw 与 SlotValue 是未填类型，没有值界证明；不把它们另作已完成结论的前提。
来源：请求复用 YiNIIface，偏移到孩子的读回复用 YiNLCtx.rd-floor；目标证书来自 YiC0Next。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDNRequests where
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiNIDomain as D
import OCF.Lean.YiNIIface as NI
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiNLCtx as C
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiKVRel as K
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_)

request : (d : D.Node) (ν : E.T) → GR.Rd (D.Node.offset d) ν
  → E.HC (E.ψ [] (E.Ωt ν) ∷ []) → NI.Request
request d ν r hc = record
  { node = d ; index = ν
  ; reads = GR.rd-child (B.sΩ B.zero) (D.Node.child d) B.zero
      (C.rd-floor (C.prefix (D.Node.offset d))
        (D.zeros (D.Node.padding d) (B.↑ B.zero (D.Node.tail d B.zero))) r)
  ; nonempty = hc }

single : NI.Request → NI.Family
single r = record { Member = ⊤ ; request = λ _ → r }

opaque
  slot-hc : E.HC (E.ψ [] (E.Ωt N.slot) ∷ [])
  slot-hc = subst E.HC N.row₁-shape (XI.back N.row₁-hc)

slot-request : (d : D.Node) → GR.Rd (D.Node.offset d) N.slot → NI.Request
slot-request d r = request d N.slot r slot-hc

slot-family : (d : D.Node) → GR.Rd (D.Node.offset d) N.slot → NI.Family
slot-family d r = single (slot-request d r)

slot-index : ∀ d r → NI.Request.index (NI.Family.request (slot-family d r) tt) ≡ N.slot
slot-index d r = refl

SlotValue : D.Node → Set
SlotValue d = RT.Rt slot-hc ≼ K.readRW (D.output d)

SlotLaw : (d : D.Node) → GR.Rd (D.Node.offset d) N.slot → Set
SlotLaw d r = NI.Law (slot-family d r)

value→law : ∀ d r → SlotValue d → SlotLaw d r
value→law d r v _ = v

law→value : ∀ d r → SlotLaw d r → SlotValue d
law→value d r law = law tt
```
