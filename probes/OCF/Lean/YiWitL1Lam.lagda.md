# 第 1 层的下界搬到 Λ 的闭项上 (搬到收缩见证的折叠)

验收文件. [YiL1Lam](YiL1Lam.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Lam where

import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiWitL1Base using (Xψ₁; Xψ₁≼ʷ)
open import OCF.Lean.YiWitIntoTw3 using (T⁺ʷ≼TΛ)

Xψ₁≼TΛ : Xψ₁ ≼ NA.read WF.TΛ
Xψ₁≼TΛ = ≼-trans Xψ₁≼ʷ T⁺ʷ≼TΛ
```
