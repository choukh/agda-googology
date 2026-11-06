# 构造 `OTFacts`

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.FactsImpl` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Assumption 4.3 的 58 条句法事实全部已证（[Linear](Linear.lagda.md)、[Trans](Trans.lagda.md)、[Facts1](Facts1.lagda.md)、[Facts2](Facts2.lagda.md)、[Facts3](Facts3.lagda.md)）。本文件把它们装进记录，`--safe --cubical-compatible`，无 postulate。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.FactsImpl where

open import OCF.Align.EboLean.OT.WO.Facts

import OCF.Align.EboLean.OT.Linear as L
import OCF.Align.EboLean.OT.Trans  as T
import OCF.Align.EboLean.OT.Facts1 as F1
import OCF.Align.EboLean.OT.Facts2 as F2
import OCF.Align.EboLean.OT.Facts2b as F2b
import OCF.Align.EboLean.OT.Facts3 as F3

facts : OTFacts
facts = record
  { ≺-irrefl      = L.≺-irrefl
  ; ≺-trans       = T.≺-trans
  ; ≺-trich       = L.≺-trich
  ; 0⪯            = F1.0⪯
  ; ⪯-prefix      = F1.⪯-prefix
  ; ⪯-app         = F1.⪯-app
  ; ⪯-φˡ          = F1.⪯-φˡ
  ; ⪯-φʳ          = F1.⪯-φʳ
  ; ⪯-Ω           = F1.⪯-Ω
  ; ψ≺κ           = F1.ψ≺κ
  ; κ⁻≺ψ          = F1.κ⁻≺ψ
  ; κ⁻≺κ          = F1.κ⁻≺κ
  ; one⪯P         = F1.one⪯P
  ; between-app   = F1.between-app
  ; φ-cmp         = F1.φ-cmp
  ; φ≺G           = F1.φ≺G
  ; Fi≺Ω⇒⪯        = F1.Fi≺Ω⇒⪯
  ; Ω-mono⁻       = F1.Ω-mono⁻
  ; ψ≺Car⇒κ⪯      = F1.ψ≺Car⇒κ⪯
  ; C̃⇒≺ψ         = F3.C̃⇒≺ψ
  ; ≺ψ⇒C̃         = F3.≺ψ⇒C̃
  ; C̃-ψ-I         = F3.C̃-ψ-I
  ; C̃-ψ-Ω         = F3.C̃-ψ-Ω
  ; ψI-cmp        = F1.ψI-cmp
  ; Car≺κ⇒⪯κ⁻     = F1.Car≺κ⇒⪯κ⁻
  ; plus-κ⁻       = F1.plus-κ⁻
  ; κ⁻∘plus       = F1.κ⁻∘plus
  ; +-OT          = F2.+-OT
  ; tilde-OT      = F2.tilde-OT
  ; tilde⪯        = F2.tilde⪯
  ; tilde-Car     = F2.tilde-Car
  ; tilde-max     = F2.tilde-max
  ; tilde-idem    = F2.tilde-idem
  ; plus-OT       = F2.plus-OT
  ; ≺plus         = F2.≺plus
  ; plus-Car      = F2.plus-Car
  ; plus-least    = F2.plus-least
  ; tilde-plus    = F2.tilde-plus
  ; plus-form     = F2.plus-form
  ; mFi⪯          = F2b.mFi⪯
  ; Ω₁⪯R          = F1.Ω₁⪯R
  ; Ω≺Ω′          = F1.Ω≺Ω′
  ; Fi-closed-Ω   = F1.Fi-closed-Ω
  ; Car-closed-+1 = F1.Car-closed-+1
  }
```
