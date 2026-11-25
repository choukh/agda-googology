# 新主线的闭项与带表的 F2 对照块的闭项相关

> 验收文件 (不读记号), 不进成品. 编译定理, 无前提: `twᶻ n` 与 `YiVTFold.twᶜ n` 相关, `EBOᶻ` 与 `YiVTFold.EBOᶜ` 相关 (`twᶻ-R`, `EBOᶻ-R`), 所以读回 `≅` (`same-twᶻ`, `same-EBOᶻ`).
> 做法照 `YiBRTw.twᶜ-R`: [YiVTRel](YiVTRel.lagda.md) 的 `A` 代入层号与证据的关系 (`YiBRTw.tw-E`, `Λ-E`, 原样引用). 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTTw where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiMTTab using (twᶻ; EBOᶻ)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; Λ-L; Λ-E)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiVTRel using (A)
import OCF.Align.Level as L

twᶻ-R : (n : ℕ) → RelT zero F.zero (twᶻ n) (F.twᶜ n)
twᶻ-R n = proj₁ (A (tw-E n) (B₀ _) (F.B₀ _) (B₀-R (E→L (tw-E n))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (tw-L n)))

EBOᶻ-R : RelT zero F.zero EBOᶻ F.EBOᶜ
EBOᶻ-R = proj₁ (A Λ-E (B₀ _) (F.B₀ _) (B₀-R (E→L Λ-E)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R Λ-L))

same-twᶻ : (n : ℕ) → readRW (twᶻ n) L.≅ read (F.twᶜ n)
same-twᶻ n = rel≅ (twᶻ-R n)

same-EBOᶻ : readRW EBOᶻ L.≅ read F.EBOᶜ
same-EBOᶻ = rel≅ EBOᶻ-R
```
