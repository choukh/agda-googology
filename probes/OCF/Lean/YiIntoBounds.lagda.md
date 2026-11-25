# `T⁺ʷ` 的已证下界搬到 `Tw 3` 与 `TΛ` 上 (无前提)

验收文件. 编译定理: `T⁺ʷ` 的六条下界 (`ΩΩ+1ʷ`, `χ₁≼ʷ`, `X₁₂≼ʷ`, `Xω≼ʷ`, `X²≼ʷ`, `Xε≼ʷ`) 经 [YiIntoTw3](YiIntoTw3.lagda.md) 的 `T⁺ʷ≼Tw3` 搬到 `W.Tw 3`, 再经 `Tw≼TΛ 3` 搬到 `W.TΛ`. 只是下界.
最高的一条是 `Xε≼TΛ`, 参照 `Xε` 读作 ψ₀(Ω_Ω+ε_{Ω₁+1}) (读法是判断, 见 [YiShpEps](YiShpEps.lagda.md)); 前三条的参照有逐项一致证明 (`S2.ts-label`, `S2.χ1-label`, `YiShpOneLab.X₁₂-label`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiIntoBounds where

import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiIntoTw3 using (T⁺ʷ≼Tw3; T⁺ʷ≼TΛ)
open import OCF.Lean.YiDlVOne using (ΩΩ+1ʷ; χ₁≼ʷ)
open import OCF.Lean.YiShpOne using (X₁₂; X₁₂≼ʷ)
open import OCF.Lean.YiShpOmega using (Xω; Xω≼ʷ)
open import OCF.Lean.YiShpSq using (X²; X²≼ʷ)
open import OCF.Lean.YiShpEps using (Xε; Xε≼ʷ)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S2
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 1 `Tw 3`

```agda
ΩΩ+1≼Tw3 : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read (W.Tw 3)
ΩΩ+1≼Tw3 = ≼-trans ΩΩ+1ʷ T⁺ʷ≼Tw3

χ₁≼Tw3 : S2.χ 1 ≼ NA.read (W.Tw 3)
χ₁≼Tw3 = ≼-trans χ₁≼ʷ T⁺ʷ≼Tw3

X₁₂≼Tw3 : X₁₂ ≼ NA.read (W.Tw 3)
X₁₂≼Tw3 = ≼-trans X₁₂≼ʷ T⁺ʷ≼Tw3

Xω≼Tw3 : Xω ≼ NA.read (W.Tw 3)
Xω≼Tw3 = ≼-trans Xω≼ʷ T⁺ʷ≼Tw3

X²≼Tw3 : X² ≼ NA.read (W.Tw 3)
X²≼Tw3 = ≼-trans X²≼ʷ T⁺ʷ≼Tw3

Xε≼Tw3 : Xε ≼ NA.read (W.Tw 3)
Xε≼Tw3 = ≼-trans Xε≼ʷ T⁺ʷ≼Tw3
```

## 2 `TΛ`

```agda
ΩΩ+1≼TΛ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.TΛ
ΩΩ+1≼TΛ = ≼-trans ΩΩ+1ʷ T⁺ʷ≼TΛ

χ₁≼TΛ : S2.χ 1 ≼ NA.read W.TΛ
χ₁≼TΛ = ≼-trans χ₁≼ʷ T⁺ʷ≼TΛ

X₁₂≼TΛ : X₁₂ ≼ NA.read W.TΛ
X₁₂≼TΛ = ≼-trans X₁₂≼ʷ T⁺ʷ≼TΛ

Xω≼TΛ : Xω ≼ NA.read W.TΛ
Xω≼TΛ = ≼-trans Xω≼ʷ T⁺ʷ≼TΛ

X²≼TΛ : X² ≼ NA.read W.TΛ
X²≼TΛ = ≼-trans X²≼ʷ T⁺ʷ≼TΛ

Xε≼TΛ : Xε ≼ NA.read W.TΛ
Xε≼TΛ = ≼-trans Xε≼ʷ T⁺ʷ≼TΛ
```
