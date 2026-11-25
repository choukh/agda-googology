# 已有累计参照与第1项的比较
验收文件；既有累计下界族的每一项在项序与序数值上严格低于实际 fs1，反向比较不可填。
这不提供实际部分和的上界，不否定 FirstRow 或 NF/G 步进；只定位旧累计界不能经项序单调性推出目标。
来源：既有下界直接复用 YiOLBoost.partial-certificate；值比较复用 YiCFMono.mono<ⁿ 与 YiNFO.s≼-irrefl。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGBKnown where
open import Data.Nat using (ℕ; suc)
open import Data.List using ([]; _∷_; replicate)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiGBStart
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiOLBoost as OB
import OCF.Lean.YiVTANLim as VL
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiIRTarget as IR
import OCF.Lean.YiRefTw2 as R
import OCF.Lean.YiExInst as XI
import OCF.Align.Level as L
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Lean.YiNFO using (s≼-irrefl)
open import OCF.Align.Value using (_≼_; ≼-trans)

known : ℕ → E.T
known n = replicate (suc n) (E.ψ [] VL.argω)
known-certificate : ∀ n → K.M⁰ (known n) (AZ.P n)
known-certificate = OB.partial-certificate
known-NF : ∀ n → NF (known n)
known-NF n = nf-rep (nf-hd VL.nωᴮ) (suc n)
known-HC : ∀ n → E.HC (known n)
known-HC n = OB.rep-hc (suc n)
known<fs1 : ∀ n → known n E.<ᵀ fs1
known<fs1 n = E.hd< (E.ar< (E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))))
¬reverse : ∀ n → ¬ (fs1 ≤ᵀ known n)
¬reverse n le = <ᵀ-irrefl (<-≤ (known<fs1 n) le)
nonempty : ∀ n → E.HC (known n) × SI.E.HC fs1
nonempty n = known-HC n , IR.term-hc 1
known-strict : ∀ n (h : E.HC fs1) (k : E.HC (known n)) → L.suc (R.Rt k) ≼ R.Rt h
known-strict n h k = mono<ⁿ (known-NF n) fs1-NF (c∷ c[]) k h (known<fs1 n)
¬value-reverse : ∀ n (h : E.HC fs1) (k : E.HC (known n)) → ¬ (R.Rt h ≼ R.Rt k)
¬value-reverse n h k rev = s≼-irrefl (R.Rt k) (≼-trans (known-strict n h k) rev)
value-nonempty : ∀ n → E.HC (known n) × E.HC fs1
value-nonempty n = known-HC n , XI.back (IR.term-hc 1)
```
