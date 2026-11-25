# 最小表实例: Tw

参数化（工程）的最小表实例；验收文件。来源 `YiVTTw`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinTw where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiMTTab using (twᶻ; EBOᶻ)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiPMFold
import OCF.Lean.YiPMTable as F
module PF = OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; Λ-L; Λ-E)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiPMMinRel using (A)
import OCF.Align.Level as L

twᶻ-R : (n : ℕ) → RelT zero F.zero (twᶻ n) (PF.twᶜ n)
twᶻ-R n = proj₁ (A (tw-E n) (B₀ _) (F.B₀ _) (B₀-R (E→L (tw-E n))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (tw-L n)))

EBOᶻ-R : RelT zero F.zero EBOᶻ PF.EBOᶜ
EBOᶻ-R = proj₁ (A Λ-E (B₀ _) (F.B₀ _) (B₀-R (E→L Λ-E)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R Λ-L))

same-twᶻ : (n : ℕ) → readRW (twᶻ n) L.≅ read (PF.twᶜ n)
same-twᶻ n = rel≅ (twᶻ-R n)

same-EBOᶻ : readRW EBOᶻ L.≅ read PF.EBOᶜ
same-EBOᶻ = rel≅ EBOᶻ-R
```
