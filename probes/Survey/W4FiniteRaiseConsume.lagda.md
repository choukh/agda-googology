# b₂ 进入接收正槽的第一次完整迭代

第四层。第 4 层正槽的单位指数迭代已严格超过 b₂，继续用同一实际种子和接收环境求 Ω 指数所得的值又严格更大，两个值都在 W4 内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseConsume where

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
open import WVOne using (T₀)
import B13FiniteLift as Lift
import WKTower as Tower
import Survey.W4FiniteRaiseWindow as Window
open Window using (module Live)
import B13FiniteClosed as Covered
import Survey.W4PTOFinite as PTO
open import OCF.Lean.YiRefTw2 using (Rt)
import Survey.EboPTOFinite as B

opaque
  floor : T₀
  floor = Rt (B.tower-h 2 2)
  calibrated : Lift.Bound (Tower.gL 2) floor
  calibrated = PTO.two-in-run

  base : L.suc (Rt (B.tower-h 2 2)) ≼ Live.small 2
  base = Live.inherited 2 floor calibrated Covered.middle-covered
```
