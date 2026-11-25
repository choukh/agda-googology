# 最小实例: `YiMTValue.norel` 的那一处, 换成带表的 F2 对照块后相关

> 验收文件 (不读记号), 不进成品. 编译定理, 无前提: 塔第 1 项的顶层, 目标第 0 层经孩子 0, 树是 "1 嵌在孩子 0" (`YiMTValue.x₁`, `x₁′`, `rx`, 原样引用): 新主线那一行的输出与 [YiVTFold](YiVTFold.lagda.md) 的同一行的输出满足 `RelT` (`rel-x₁`).
> 对照: 同一陈述对原 F2 的回退行为假 (`YiMTValue.norel`). 这里是 [YiVTRel](YiVTRel.lagda.md) 的 `S` 的一个代入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTNorel where

open import Data.Product using (proj₁)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiMTValue using (x₁; x₁′; rx)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E)
open import OCF.Lean.YiVTRel using (S)

rel-x₁ : RelT zero F.zero
           (proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (inc zero self) (Ωt zero) x₁))
           (F.ψs (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) (F.B₀ (F.tw 1)) F.zero (F.inb F.zero F.self) (F.Ωt F.zero) (F.Ωt-nz F.zero) x₁′)
rel-x₁ = proj₁ (S (tw-E 1) (B₀ (tw 1)) (F.B₀ (F.tw 1)) (B₀-R (tw-L 1)) (wincΩ iz wself) (Ωt zero) (Ωt-R lz) (Ωn-R lz) rx)
```
