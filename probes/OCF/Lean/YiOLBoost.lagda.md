# 实际链点1超过既有最高参照的值下界
验收文件；big 为既有最高参照的折叠参数末尾加1，全部HC的at-one与严格增长strict-output已编译。
实际底、表与链均取YiE4原实例；不声称ψ₀(Ω_{Ω₂})或第3站完成。
来源：YiOLSum 的累计拼接，YiVTRel.A/cumΩ-R 的实际底桥，YiVTANEnd.tN≼br2 与 YiVTANLim 的共尾下界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOLBoost where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; replicate)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
import OCF.Lean.YiOLSum as M
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F0
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiE4Default as DF
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as R2
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiVTRel as VR
import OCF.Lean.YiVTEBShape as VT
import OCF.Lean.YiVTANEnd as AN
import OCF.Lean.YiVTANLim as AL
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRTw using (Λ-E; Λ-L)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; cumΩ-R)
open import OCF.Lean.YiBRValue using (up≼)
open import OCF.Lean.YiNFO using (mono<; ↓suc)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTree as ET
import OCF.Align.StandardOmega as NO
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; l≼; ≼l)
opaque
  beta-eq : AZ.D.β ≡ GI.betaᴱ 3
  beta-eq = trans AZ.D.β-eq (DF.beta-eq 3)
  raw-beta-R : RelT B.zero F.zero (proj₁ (GI.betaᴱ 3))
    (F.ψ⊥ F.Λ F.Ev-Λ F.Rt-Λ (F.B₀ F.Λ) (F.cumΩ F.tw 2))
  raw-beta-R = proj₁ (VR.A Λ-E (F0.B₀ _) (F.B₀ _) (B₀-R Λ-L) (O.Ωt B.zero)
    (Ωt-R lz) (Ωn-R lz) (cumΩ-R Λ-L 2))
  beta-R : RelT B.zero F.zero (proj₁ AZ.D.β) (VT.br 2)
  beta-R = subst (λ x → RelT B.zero F.zero (proj₁ x) (VT.br 2)) (sym beta-eq)
    (subst (λ x → RelT B.zero F.zero (proj₁ (GI.betaᴱ 3)) x) (VT.branch-eq 2) raw-beta-R)
tN-base : ∀ m (h : E.HC (AN.tN m)) → R2.Rt h ≼ K.readRW (proj₁ AZ.D.β)
tN-base m h = ≼-trans (up≼ beta-R (AN.tN≼br2 m h)) (CS.rr≼ (proj₁ AZ.D.β))
tω-base : (h : E.HC AL.tω) → R2.Rt h ≼ K.readRW (proj₁ AZ.D.β)
tω-base (E.h0 ())
tω-base (E.h1 () _)
tω-base (E.hω _ hs) = l≼ (λ n → ≼-trans
  (↓suc (mono< (AL.nfω n) (AN.nN₁ n) (hs n) (AN.hN n) (AL.lt n))) (tN-base n (AN.hN n)))
m-base : K.M⁰ AL.tω (proj₁ AZ.D.β)
m-base = CS.sem→M⁰ AL.hΩω (proj₁ AZ.D.β) (tω-base AL.hΩω)
big : E.T
big = E.ψ [] (E.sucT AL.argω) ∷ []
m-next : K.M⁰ big (proj₁ (O.next⁺ AZ.D.β))
m-next = K.G⁰.m-next {t = big} {p = E.ψ [] AL.argω} AZ.D.β refl (λ n → refl) m-base
bound : (h : SI.E.HC big) → SI.E.tree h ≼ K.readRW (proj₁ AZ.D.output)
bound h = ≼-trans (XI.tree-back h) (≼-trans (K.lower⁰ m-next (XI.back h)) M.next-output)

principal : ∀ {x xs} → NO.NF₁ (x ∷ xs) → NO.NFᴾ₁ x
principal (NO.n∷ p _ _) = p
ct-rep : ∀ n → EB.Ctbl (replicate n (E.ψ [] AL.argω))
ct-rep zero = EB.c[]
ct-rep (suc n) = EB.c∷ (ct-rep n)
-- perf: S-1/S-3，具体参照证书在出生处封装。
opaque
  rep-hc : ∀ n → E.HC (replicate n (E.ψ [] AL.argω))
  rep-hc n = ET.hc (EB.nf-rep (EB.nf-hd AL.nωᴮ) n) (ct-rep n)
  big-hc : E.HC big
  big-hc = E.hω refl rep-hc

-- perf: C-9/C-10，先在变量参照证书上比较两项。
two-strict : (a : E.T) → NO.NF₁ (E.ψ [] a ∷ [])
  → (h : E.HC (E.ψ [] a ∷ []))
  → (h₂ : E.HC (replicate 2 (E.ψ [] a))) → L.suc (R2.Rt h) ≼ R2.Rt h₂
two-strict a n h h₂ = mono< {s = E.ψ [] a ∷ []} {t = replicate 2 (E.ψ [] a)}
  n (NO.NF₁-rep {x = E.ψ [] a} (principal {x = E.ψ [] a} {xs = []} n) 2) h h₂ (E.tl< E.[]<)
strict-output : L.suc (R2.Rt AL.hΩω) ≼ K.readRW (proj₁ AZ.D.output)
strict-output = ≼-trans (two-strict AL.argω AL.nω₁ AL.hΩω (rep-hc 2))
  (≼-trans (K.lower⁰ {t = replicate 2 (E.ψ [] AL.argω)}
    (K.G⁰.m-rep {p = E.ψ [] AL.argω} m-base 1) (rep-hc 2))
    (≼-trans (≼l 1 (≼-refl _)) M.next-output))
at-one : (h : SI.E.HC big) → SI.E.tree h ≼ K.readRW (proj₁
  (FR.Step.out 2 (FR.Step.chain 2 1)))
at-one = DF.move-bound refl DF.output-old bound

partial-certificate : ∀ n → K.M⁰ (replicate (suc n) (E.ψ [] AL.argω)) (AZ.P n)
partial-certificate n = CS.sem→M⁰ (rep-hc (suc n)) (AZ.P n)
  (≼-trans (K.lower⁰ (K.G⁰.m-rep {p = E.ψ [] AL.argω} m-base n) (rep-hc (suc n)))
    (≼-trans (M.U.iter-read n) (M.U.partial n)))
-- perf: C-9，重输出的等式输运在变量上定义，再实例化。
move-value : (Y : L.Ordᶜ L.zero) (u v : O.Tr⁺ B.zero) → u ≡ v
  → Y ≼ K.readRW (proj₁ u) → Y ≼ K.readRW (proj₁ v)
move-value Y u .u refl low = low
strict-at-one : L.suc (R2.Rt AL.hΩω) ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 1)))
strict-at-one = move-value (L.suc (R2.Rt AL.hΩω)) AZ.D.output
  (FR.Step.out 2 (FR.Step.chain 2 1)) DF.output-old strict-output
ebo-lower : (h : SI.E.HC big) → SI.E.tree h ≼ K.readRW MT.EBOᶻ
ebo-lower h = ≼-trans (at-one h) (≼-trans (FR.Step.branch-upper 2 1) (GE.upperᴱ 3))
strict-ebo : L.suc (R2.Rt AL.hΩω) ≼ K.readRW MT.EBOᶻ
strict-ebo = ≼-trans strict-at-one (≼-trans (FR.Step.branch-upper 2 1) (GE.upperᴱ 3))
```
