# 诊断：上界 (V122) 搬到主线精简块

> 诊断：上界, 不进成品, 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 精简块上的最小见证 `Witᴿ` (`up β two (Ωt 2)`) 与 F2 的同名树相关 (`wit-R`), 所以两边折叠的读回 `≅` (`same-V`).
> 于是 [YiDropRow](YiDropRow.lagda.md) 的下界原样落在主线上: `row≼Vᴿ`, `lvl≼Vᴿ`, `naive≼Vᴿ`. 不否定 V122 的上界; 它们是那条上界的第一个障碍.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDropRW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
import OCF.Lean.YiLegBlock as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; ψ₀-R; ⊕-L; ↑-L)
open import OCF.Lean.YiBRValue using (readRW; rel≅; up≼)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiLSTw1 using (G; lvl)
import OCF.Lean.YiDropRow as DR
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
```

## 见证与关系

孩子 two 的层号是 `tw 0 ⊕ ↑ (tw 0) two`, 与 F2 的 `h₁ two` 由 `tw-L 1` 的分支相关.

```agda
twoᴿ : Tr zero
twoᴿ = suc (suc zero)

Witᴿ : Tr (tw 1)
Witᴿ = up (proj₁ (Ωt (tw 1))) twoᴿ (proj₁ (Ωt (tw 0 ⊕ ↑ (tw 0) twoᴿ))) (proj₂ (Ωt (tw 0 ⊕ ↑ (tw 0) twoᴿ)))

Vᴿ : Tr zero
Vᴿ = proj₁ (ψ₀ (tw 1) (Ok-tw 1) Witᴿ)

wit-R : RelT (tw 1) (F.tw 1) Witᴿ DR.Wit
wit-R = iu (Ωt-R (tw-L 1) , (is (is iz) , Ωt-R rl , Ωn-R rl))
  where
  rl = ⊕-L (tw-L 0) (↑-L (tw-L 0) (is (is iz)))

V-R : RelT zero F.zero Vᴿ DR.V
V-R = ψ₀-R (tw-E 1) wit-R

same-V : readRW Vᴿ L.≅ read DR.V
same-V = rel≅ V-R
```

## 主线上的下界

```agda
row≼Vᴿ : ∀ n → read (G (DR.ch n)) ≼ readRW Vᴿ
row≼Vᴿ n = up≼ V-R (DR.row≼V n)

lvl≼Vᴿ : L.ψ⁰ (L.Ω (lvl DR.c₁)) ≼ readRW Vᴿ
lvl≼Vᴿ = up≼ V-R DR.lvl≼V

naive≼Vᴿ : L.ψ⁰ (L.Ω (L.suc (lvl DR.E₀))) ≼ readRW Vᴿ
naive≼Vᴿ = up≼ V-R DR.naive≼V
```
