# 第 1 层的下界搬到 Λ 的闭项上

验收文件. 编译定理, 无前提: `Xψ₁≼TΛ : Xψ₁ ≼ NA.read W.TΛ`, 由 [YiL1Base](YiL1Base.lagda.md) 的 `Xψ₁≼ʷ` 与 [YiIntoTw3](YiIntoTw3.lagda.md) 的 `T⁺ʷ≼TΛ` 复合. 参照 `Xψ₁` 读作 ψ₀(Ω_Ω+ψ₁(Ω_Ω)), 读法是判断 (没有逐项一致证明). 主审 2026-11-12 写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiL1Lam where

import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiL1Base using (Xψ₁; Xψ₁≼ʷ)
open import OCF.Lean.YiIntoTw3 using (T⁺ʷ≼TΛ)

Xψ₁≼TΛ : Xψ₁ ≼ NA.read W.TΛ
Xψ₁≼TΛ = ≼-trans Xψ₁≼ʷ T⁺ʷ≼TΛ
```
