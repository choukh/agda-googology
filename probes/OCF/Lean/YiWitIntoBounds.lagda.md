# `T⁺ʷ` 的已证下界搬到 `Tw 3` 与 `TΛ` 上 (无前提) (搬到收缩见证的折叠)

验收文件. [YiIntoBounds](YiIntoBounds.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitIntoBounds where

import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiWitIntoTw3 using (T⁺ʷ≼Tw3; T⁺ʷ≼TΛ)
open import OCF.Lean.YiWitVOne using (ΩΩ+1ʷ; χ₁≼ʷ)
open import OCF.Lean.YiWitShpOne using (X₁₂; X₁₂≼ʷ)
open import OCF.Lean.YiWitShpOmega using (Xω; Xω≼ʷ)
open import OCF.Lean.YiWitShpSq using (X²; X²≼ʷ)
open import OCF.Lean.YiWitShpEps using (Xε; Xε≼ʷ)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S2
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 1 `Tw 3`

```agda
ΩΩ+1≼Tw3 : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read (WF.Tw 3)
ΩΩ+1≼Tw3 = ≼-trans ΩΩ+1ʷ T⁺ʷ≼Tw3

χ₁≼Tw3 : S2.χ 1 ≼ NA.read (WF.Tw 3)
χ₁≼Tw3 = ≼-trans χ₁≼ʷ T⁺ʷ≼Tw3

X₁₂≼Tw3 : X₁₂ ≼ NA.read (WF.Tw 3)
X₁₂≼Tw3 = ≼-trans X₁₂≼ʷ T⁺ʷ≼Tw3

Xω≼Tw3 : Xω ≼ NA.read (WF.Tw 3)
Xω≼Tw3 = ≼-trans Xω≼ʷ T⁺ʷ≼Tw3

X²≼Tw3 : X² ≼ NA.read (WF.Tw 3)
X²≼Tw3 = ≼-trans X²≼ʷ T⁺ʷ≼Tw3

Xε≼Tw3 : Xε ≼ NA.read (WF.Tw 3)
Xε≼Tw3 = ≼-trans Xε≼ʷ T⁺ʷ≼Tw3
```

## 2 `TΛ`

```agda
ΩΩ+1≼TΛ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read WF.TΛ
ΩΩ+1≼TΛ = ≼-trans ΩΩ+1ʷ T⁺ʷ≼TΛ

χ₁≼TΛ : S2.χ 1 ≼ NA.read WF.TΛ
χ₁≼TΛ = ≼-trans χ₁≼ʷ T⁺ʷ≼TΛ

X₁₂≼TΛ : X₁₂ ≼ NA.read WF.TΛ
X₁₂≼TΛ = ≼-trans X₁₂≼ʷ T⁺ʷ≼TΛ

Xω≼TΛ : Xω ≼ NA.read WF.TΛ
Xω≼TΛ = ≼-trans Xω≼ʷ T⁺ʷ≼TΛ

X²≼TΛ : X² ≼ NA.read WF.TΛ
X²≼TΛ = ≼-trans X²≼ʷ T⁺ʷ≼TΛ

Xε≼TΛ : Xε ≼ NA.read WF.TΛ
Xε≼TΛ = ≼-trans Xε≼ʷ T⁺ʷ≼TΛ
```
