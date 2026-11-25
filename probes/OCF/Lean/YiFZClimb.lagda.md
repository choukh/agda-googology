# EBOᶻ 的第二个后继值下界
验收文件；尝试把已有 EBOᶻ 下界再提高一个后继。
构造复用变量参照证书和 fold 保持，树定义不变。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFZClimb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; replicate)
open import Data.Product using (proj₁)
open import OCF.Align.Value using (_≼_; s≼s; ≼-trans; ≼-refl; ≼l)
import OCF.Align.Level as L
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiNFO as NF
import OCF.Align.StandardOmega as SO
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRefTw2 as R2
import OCF.Lean.YiVTANLim as VT
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiE4Default as DF
import OCF.Lean.YiOLSum as M
import OCF.Lean.YiOLBoost as OL
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiMTTab as MT

p : E.PT
p = E.ψ [] VT.argω

rep-step : (n : ℕ) → replicate n p E.<ᵀ replicate (suc n) p
rep-step zero    = E.[]<
rep-step (suc n) = E.tl< (rep-step n)

principal : SO.NFᴾ₁ p
principal = OL.principal {x = p} {xs = []} VT.nω₁

rep-advance : (n : ℕ) → L.suc (R2.Rt (OL.rep-hc (suc n))) ≼ R2.Rt (OL.rep-hc (suc (suc n)))
rep-advance n = NF.mono<
  {s = replicate (suc n) p} {t = replicate (suc (suc n)) p}
  (SO.NF₁-rep {x = p} principal (suc n))
  (SO.NF₁-rep {x = p} principal (suc (suc n)))
  (OL.rep-hc (suc n)) (OL.rep-hc (suc (suc n))) (rep-step (suc n))

bound-three-copies : R2.Rt (OL.rep-hc 3) ≼ K.readRW (proj₁ AZ.D.output)
bound-three-copies = ≼-trans
  (K.lower⁰ {t = replicate 3 p}
    (K.G⁰.m-rep {p = p} OL.m-base 2) (OL.rep-hc 3))
  (≼-trans (≼l 2 (≼-refl _)) M.next-output)

strict-output₂ : L.suc (L.suc (R2.Rt VT.hΩω)) ≼ K.readRW (proj₁ AZ.D.output)
strict-output₂ = ≼-trans
  (≼-trans (s≼s (OL.two-strict VT.argω VT.nω₁ VT.hΩω (OL.rep-hc 2)))
            (rep-advance 1))
  bound-three-copies

strict-at-one₂ : L.suc (L.suc (R2.Rt VT.hΩω)) ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 1)))
strict-at-one₂ = OL.move-value (L.suc (L.suc (R2.Rt VT.hΩω)))
  AZ.D.output (FR.Step.out 2 (FR.Step.chain 2 1)) DF.output-old strict-output₂

strict-ebo₂ : L.suc (L.suc (R2.Rt VT.hΩω)) ≼ K.readRW MT.EBOᶻ
strict-ebo₂ = ≼-trans strict-at-one₂
  (≼-trans (FR.Step.branch-upper 2 1) (GE.upperᴱ 3))
```
