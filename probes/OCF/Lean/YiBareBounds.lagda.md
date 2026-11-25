# 裸折叠: `T⁺ʷᵇ` 的已证下界搬到 `Twᵇ 3` 与 `TΛᵇ` 上 (无前提)

验收文件. 编译定理: 四条下界 (`ΩΩ+1ʷ`, `χ₁≼ʷ`, `X₁₂≼ʷ`, `Xω≼ʷ`) 经 [YiBareIntoTw3](YiBareIntoTw3.lagda.md) 的 `T⁺ʷ≼Tw3` 搬到 `W.Twᵇ 3`, 再到 `W.TΛᵇ`; 照 [YiIntoBounds](YiIntoBounds.lagda.md). 只是下界.
最高的一条是 `Xω≼TΛ`, 参照 `Xω` 读作 ψ₀(Ω_Ω+Ω₁·ω) (读法是判断). 原文的 `X²≼TΛ`, `Xε≼TΛ` 在裸折叠上没有对应的定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBareBounds where

import OCF.Lean.YiBareFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiBareIntoTw3 using (T⁺ʷ≼Tw3; T⁺ʷ≼TΛ)
open import OCF.Lean.YiBareVOne using (ΩΩ+1ʷ; χ₁≼ʷ)
open import OCF.Lean.YiBareShpOne using (X₁₂; X₁₂≼ʷ)
open import OCF.Lean.YiBareShpOmega using (Xω; Xω≼ʷ)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S2
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 1 `Twᵇ 3`

```agda
ΩΩ+1≼Tw3 : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read (W.Twᵇ 3)
ΩΩ+1≼Tw3 = ≼-trans ΩΩ+1ʷ T⁺ʷ≼Tw3

χ₁≼Tw3 : S2.χ 1 ≼ NA.read (W.Twᵇ 3)
χ₁≼Tw3 = ≼-trans χ₁≼ʷ T⁺ʷ≼Tw3

X₁₂≼Tw3 : X₁₂ ≼ NA.read (W.Twᵇ 3)
X₁₂≼Tw3 = ≼-trans X₁₂≼ʷ T⁺ʷ≼Tw3

Xω≼Tw3 : Xω ≼ NA.read (W.Twᵇ 3)
Xω≼Tw3 = ≼-trans Xω≼ʷ T⁺ʷ≼Tw3
```

## 2 `TΛᵇ`

```agda
ΩΩ+1≼TΛ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.TΛᵇ
ΩΩ+1≼TΛ = ≼-trans ΩΩ+1ʷ T⁺ʷ≼TΛ

χ₁≼TΛ : S2.χ 1 ≼ NA.read W.TΛᵇ
χ₁≼TΛ = ≼-trans χ₁≼ʷ T⁺ʷ≼TΛ

X₁₂≼TΛ : X₁₂ ≼ NA.read W.TΛᵇ
X₁₂≼TΛ = ≼-trans X₁₂≼ʷ T⁺ʷ≼TΛ

Xω≼TΛ : Xω ≼ NA.read W.TΛᵇ
Xω≼TΛ = ≼-trans Xω≼ʷ T⁺ʷ≼TΛ
```
