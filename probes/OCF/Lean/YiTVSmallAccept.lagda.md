# Ψ 的小例末端验收
验收文件；small-NΨ 检查阈值 1 与目标 ψ₀(Ω₁) 的固定小例，前提由 small-input 实填。
来源：YiTBFam.sΩ-LF 的有限层号实例与 YiKVRel.lower⁰；不把固定小例说成全称 NΨ。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTVSmallAccept where
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as M
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTCValue as C
import OCF.Lean.YiTVPsi as Q
open import OCF.Lean.YiTVRead
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiCLLow as CL
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Align.Value as W
import OCF.Align.Level as L

v : V.V B.zero
v = V.val B.zero (proj₁ (O.Ωt B.zero))
hv : V.LegV B.zero v
hv = V.val-leg B.zero (proj₁ (O.Ωt B.zero))
small-input : V.val B.zero (proj₁ (O.Ωt B.zero)) V.≼ v
small-input = V.≼-refl _
small-target : E.T
small-target = E.ψ [] (E.Ωt (E.natT 1)) ∷ []
small-relation : K.M⁰ small-target (proj₁ (C.collapseᵛ B.zero (P.Ok-tw 0) v hv))
small-relation = TF.sΩ-LF {n = 0} {j = 0} (proj₂ (P.Ok-tw 1) (B.suc B.zero))
  (M.rbᶻ K.one) (RF.tu (RF.can CL.s0)) (F.B₀ K.one) (O.Ωt B.zero)
  (λ i u → K.⊴r) (K.m1 refl K.mz)
small-NΨ : V.val B.zero (proj₁ (O.Ωt B.zero)) V.≼ v →
  (h : SI.E.HC small-target) → SI.E.tree h W.≼ readV (Q.Ψ B.zero (P.Ok-tw 0) v hv)
small-NΨ input h = W.≼-trans (XI.tree-back h)
  (W.≼-trans (K.lower⁰ small-relation (XI.back h))
    (W.≅→≼ (L.≅-sym (read-val (proj₁ (C.collapseᵛ B.zero (P.Ok-tw 0) v hv))))))
small-hc : SI.E.HC small-target
small-hc = SI.conv (ET.hc-tower 1)
small-result : SI.E.tree small-hc W.≼ readV (Q.Ψ B.zero (P.Ok-tw 0) v hv)
small-result = small-NΨ small-input small-hc
```
