# 换基干净对象的第 0 项
验收文件；第 0 项 ψ₀(Ω_Ω) 的下界，累计见证为 1；不涉及第 1 项。
来源：YiC0Connect 的 BTBO 出口、YiC0Reduce 的下降拼接；实际折叠为 YiBSFold。
证明仍经 F2 块对应，换基地板以上的行未用于本项值界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTZero where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiBTGoals as G
import OCF.Lean.YiBTLocal as C
import OCF.Lean.YiBTDesc as D
import OCF.Lean.YiBTPremise as P
import OCF.Lean.YiBTRel as R
import OCF.Lean.YiC0Local as Old
import OCF.Lean.YiC0Connect as OC
import OCF.Lean.YiC0Node as N
import OCF.Lean.YiC0Rows as Rows
import OCF.Lean.YiLegBlock as L
import OCF.Lean.YiLegFold as L
import OCF.Lean.YiBRFold as BF
import OCF.Lean.YiBRLem as BL
import OCF.Lean.YiBROps as BO
import OCF.Lean.YiBRValue as BV
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiEXRow as XR
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Align.YiBtValBT as BT
open import OCF.Lean.YiBRRel using (RelT; is; iz; ds)
open import OCF.Align.Value using (_≼_; ≼-trans)
opaque
  hc₀ : E.HC G.row₀
  hc₀ = XI.back G.nonempty₀
  neck-out : O.Tr⁺ B.zero
  neck-out = BS.ψ₀ Old.neck C.o-neck C.r-neck (proj₁ (O.Ωt Old.neck))
  neck-out-eq : neck-out ≡ BS.ψ₀ Old.neck C.o-neck C.r-neck (proj₁ (O.Ωt Old.neck))
  neck-out-eq = refl
output-R : RelT B.zero L.zero
  (proj₁ (BS.ψ₀ Old.neck C.o-neck C.r-neck (proj₁ (O.Ωt Old.neck)))) N.output
output-R = proj₁ (R.topΩ {tb = C.r-neck} P.node-E OC.no-child (F.B₀ Old.neck) (L.B₀ N.ΩN)
  (BF.B₀-R (BL.E→L P.node-E)) (O.Ωt B.zero) (is iz) ds
  (λ z → R.u0 z _ _) (BO.Ωt-R (BL.E→L P.node-E)))
neck-btbo : BT.D.BTBOᴵ ≼ K.readRW (proj₁ neck-out)
neck-btbo = subst (λ z → BT.D.BTBOᴵ ≼ K.readRW (proj₁ z)) (sym neck-out-eq)
  (≼-trans (BV.up≼ output-R Rows.btbo)
    (CS.rr≼ (proj₁ (BS.ψ₀ Old.neck C.o-neck C.r-neck (proj₁ (O.Ωt Old.neck))))))
neck-low : RT.Rt hc₀ ≼ K.readRW (proj₁ neck-out)
neck-low = ≼-trans (RT.tree-≼ refl hc₀ (ET.hc-tower 2)) (≼-trans XR.row₂-btbo neck-btbo)
neck-below : K.readRW (proj₁ neck-out) ≼ K.readRW (proj₁ (U.Inner.out C.c₁))
neck-below = subst (λ z → K.readRW (proj₁ z) ≼ K.readRW (proj₁ (U.Inner.out C.c₁)))
  (sym neck-out-eq)
  (subst (λ z → K.readRW (D.F₀ Old.neck C.o-neck C.r-neck) ≼ K.readRW (proj₁ z))
    (sym C.child-output) (D.read-desc C.neck-path (proj₂ U.o₂ C.c₁) (proj₂ U.r₂ C.c₁)))
need : K.M⁰ G.row₀ (proj₁ (U.Inner.out C.c₁))
need = CS.sem→M⁰ hc₀ (proj₁ (U.Inner.out C.c₁)) (≼-trans neck-low neck-below)
first-row : G.FirstRow
first-row = 1 , K.G⁰.m-right (proj₁ (U.Inner.out B.zero))
  (subst (λ d → K.M⁰ G.row₀ (proj₁ (U.Inner.out d))) C.c₁-eq need)
witness : proj₁ first-row ≡ 1
witness = refl
first-rel : K.M⁰ G.row₀ (proj₁ U.output)
first-rel = subst (λ z → K.M⁰ G.row₀ (proj₁ z)) (sym U.row)
  (K.mw (proj₂ first-row) (B.◃l 1))
first-value : G.Value0
first-value h = ≼-trans (XI.tree-back h) (K.lower⁰ first-rel (XI.back h))
```
