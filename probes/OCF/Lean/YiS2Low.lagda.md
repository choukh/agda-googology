# 第 2 站的实际关系连出口
验收文件；station→certificate 对实际站把 Kᴱ n 反射为关系连出口；folded² 与 low2 实填第 2 站。
来源：YiFRStations.k2 经 YiAbsSimInst.toL-tree 与 YiKCSem.sem→M⁰ 反射，再用 YiHCCheck.of⁰/ex-of⁰。
复用既有 ψ₀(Ω_Ω) 值下界，没有新增强度；不声称完成逐链保持或一般 Low。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS2Low where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as KS
import OCF.Lean.YiCNKeel as CN
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiS1Accept as SA
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiFRStations using (k2)
open import OCF.Lean.YiGIEnd using (row-eq)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_; ≼-trans)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

opaque
  hc-row : ∀ n → E.HC (Keel⁻.row keelᴱ n)
  hc-row n = subst E.HC (sym (row-eq n)) (ET.hc-tower n)

value-from-station : ∀ n → SA.Kᴱ n → Rt (hc-row n) ≼ K.readRW (Keel⁻.twc keelᴱ n)
value-from-station n kn = ≼-trans (SI.toL-tree (hc-row n)) (kn (SI.conv (hc-row n)))
raw-from-station : ∀ n → SA.Kᴱ n → K.M⁰ (Keel⁻.row keelᴱ n) (Keel⁻.twc keelᴱ n)
raw-from-station n kn = KS.sem→M⁰ (hc-row n) (Keel⁻.twc keelᴱ n) (value-from-station n kn)
station→certificate : ∀ n → SA.Kᴱ n → Σ (GR.R B.zero (Keel⁻.row keelᴱ n) (Keel⁻.twc keelᴱ n)) H.Exᴴ
station→certificate n kn = HC.of⁰ (raw-from-station n kn) , HC.ex-of⁰ (raw-from-station n kn)

h2 : E.HC (Keel⁻.row keelᴱ 2)
h2 = hc-row 2
value2 : Rt h2 ≼ K.readRW (Keel⁻.twc keelᴱ 2)
value2 = value-from-station 2 k2
raw2 : K.M⁰ (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)
raw2 = raw-from-station 2 k2
folded : GR.R B.zero (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)
folded = HC.of⁰ raw2
ex-folded : H.Exᴴ folded
ex-folded = HC.ex-of⁰ raw2
folded² : Σ (GR.R B.zero (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)) H.Exᴴ
folded² = station→certificate 2 k2
low2 : CN.LowAt 2
low2 _ = folded²
```
