# 新终点保持旧参照下界
验收文件，读记号；tω≼EBOᵗ 对全部 HC tω 证书成立，无未填前提。
来源：YiVTANEnd.lowN、YiVTEVReach.Ω≽1 与 YiVTANLim 的取极限证明；采用路线 (b)。
只比较第 2 支的实际零孩子输出；读回经 YiKCSem.rr≼ 与 YiKQSuff.read≤ 显式搬运。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNDAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
import OCF.Lean.YiCWTable as CT
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiCWStations as CS
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiVTEBShape as VT
import OCF.Lean.YiVTEVEnd as VE
import OCF.Lean.YiVTEVReach as EV
import OCF.Lean.YiVTLSTw1 as T1
import OCF.Lean.YiVTANEnd as AN
import OCF.Lean.YiVTANLim as AL
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; cumΩ-R)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBRTw using (Λ-E; Λ-L; tw-E; tw-L)
open import OCF.Lean.YiBRValue using (readRW; up≼)
import OCF.Lean.YiVTRel as VR
open import OCF.Lean.YiNDBridge using (rB1)
open import OCF.Lean.YiNDTop using (topΩ)
open import OCF.Lean.YiMTRel using (u0)
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiKQSuff using (read≤)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Lean.YiNFO using (mono<; ↓suc)
same-local : ∀ i (u : i ≤ tw 1) → C.baseᴱ 2 i (inc zero u) ≡ GI.baseᴱ 2 i (inc zero u)
same-local i u = refl
old-rB2 : RelBase (tw 2) (F.tw 2) (GI.baseᴱ 2) (VT.dB 2)
old-rB2 = VR.cL Λ-E (B₀ _) (F.B₀ _) (B₀-R Λ-L) (cumΩ-R Λ-L 1) 2
rBr0 : RelBase (tw 1) (F.tw 1) (λ i u → C.baseᴱ 2 i (inc zero u)) VE.Br0
rBr0 i i′ u u′ ru =
  subst (λ Z → RelT i i′ (proj₁ Z) (F.bs VE.Br0 i′ u′) × RelD i i′ (proj₂ Z) (F.ns VE.Br0 i′ u′))
    (sym (same-local i u)) (old-rB2 i i′ (inc zero u) (F.inb F.zero u′) (wincΩ iz ru))
beta1-R : RelT zero F.zero (proj₁ (C.betaᴱ 1)) (F.b⊥ (VT.dB 1)) × RelD zero F.zero (proj₂ (C.betaᴱ 1)) (F.n⊥ (VT.dB 1))
beta1-R = VR.A Λ-E (B₀ _) (F.B₀ _) (B₀-R Λ-L) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (cumΩ-R Λ-L 0)
beta2-R : RelT zero F.zero (proj₁ (C.betaᴱ 2)) (F.b⊥ VE.Br0) × RelD zero F.zero (proj₂ (C.betaᴱ 2)) (F.n⊥ VE.Br0)
beta2-R = topΩ {tb = proj₁ (CT.rbᵗ 1)} (tw-E 1) (C.baseᴱ 1) (VT.dB 1) rB1 (C.betaᴱ 1)
  (proj₁ beta1-R) (proj₂ beta1-R) (λ z → u0 z _ _) (Ωt-R (tw-L 1))
out0-R : RelT zero F.zero (proj₁ (C.Step.out 1 zero)) (F.ψ⊥ (F.tw 1) VE.ε′ VE.ρ′ VE.Br0 (F.Ωt (F.tw 1)))
out0-R = proj₁ (VR.A (tw-E 1) (λ i u → C.baseᴱ 2 i (inc zero u)) VE.Br0 rBr0 (C.betaᴱ 2)
  (proj₁ beta2-R) (proj₂ beta2-R) (Ωt-R (tw-L 1)))
tN≼out0 : ∀ m (h : HC (AN.tN m)) → R2.Rt h ≼ readRW (proj₁ (C.Step.out 1 zero))
tN≼out0 m h = up≼ out0-R (≼-trans (AN.lowN m h) (EV.Ω≽1 F.zero T1.h₁ VE.ε′ VE.ρ′ VE.Br0))
tN≼EBOᵗ : ∀ m (h : HC (AN.tN m)) → R2.Rt h ≼ readRW CT.EBOᵗ
tN≼EBOᵗ m h = ≼-trans (tN≼out0 m h) (≼-trans (rr≼ (proj₁ (C.Step.out 1 zero)))
  (≼-trans (CS.branch-upper 1 0) (≼-trans (CS.upper 2) (read≤ CT.EBOᵗ))))
tω≼EBOᵗ : (h : HC AL.tω) → R2.Rt h ≼ readRW CT.EBOᵗ
tω≼EBOᵗ (h0 ())
tω≼EBOᵗ (h1 () _)
tω≼EBOᵗ (hω e hs) = l≼ (λ n → ≼-trans (↓suc (mono< (AL.nfω n) (AN.nN₁ n) (hs n) (AN.hN n) (AL.lt n))) (tN≼EBOᵗ n (AN.hN n)))
inst : R2.Rt AL.hΩω ≼ readRW CT.EBOᵗ
inst = tω≼EBOᵗ AL.hΩω
```
