# 构造 `OTFacts`

Assumption 4.3 的 58 条句法事实全部已证（[Linear](Linear.lagda.md)、[Trans](Trans.lagda.md)、[Facts1](Facts1.lagda.md)、[Facts2](Facts2.lagda.md)、[Facts3](Facts3.lagda.md)）。本文件把它们装进记录，`--safe --cubical-compatible`，无 postulate。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.FactsImpl where

open import Mahlo.Inacc.WO.Facts

import Mahlo.Inacc.Linear as L
import Mahlo.Inacc.Trans  as T
import Mahlo.Inacc.Facts1 as F1
import Mahlo.Inacc.Facts2 as F2
import Mahlo.Inacc.Facts2b as F2b
import Mahlo.Inacc.Facts3 as F3

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
  ; φ-OT          = F2.φ-OT
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
  ; +1-mono       = F1.+1-mono
  ; Ωⁿ-mono       = F1.Ωⁿ-mono
  ; Ωⁿ-OT         = F1.Ωⁿ-OT
  ; mFi-Fi        = F2b.mFi-Fi
  ; mFi-OT        = F2b.mFi-OT
  ; ψI0-least     = F1.ψI0-least
  ; Fi≺ψI+1⇒⪯     = F1.Fi≺ψI+1⇒⪯
  ; Ωⁿ-bound      = F2b.Ωⁿ-bound
  ; ψκ-mono       = F1.ψκ-mono
  ; ψI-mono       = F1.ψI-mono
  ; +1-least      = F1.+1-least
  ; Fi-form       = F2b.Fi-form
  ; pFi-0         = F2b.pFi-0
  }
```
