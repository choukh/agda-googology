# YiUTTwo 输出的强值下界目标
验收目标类型；本文件只规定目标和给出到单一桥接前提的归约，不声称该前提已证。
桥接以 `YiVNTwo.output-lower` 的现有值下界为出口，不使用下标值序单调。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFZGoal where

open import Data.Product using (proj₁)
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Align.Level as L
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiUTTwo as UT
import OCF.Lean.YiRefTw2 as R2
import OCF.Lean.YiVTANLim as AL
import OCF.Lean.YiVWVal as W
import OCF.Lean.YiVNIdx as N
import OCF.Lean.YiVNTwo as VN

yiut-two-above-current : Set
yiut-two-above-current =
  L.suc (L.suc (R2.Rt AL.hΩω)) ≼ K.readRW (proj₁ UT.output)

bridge-to-notation : Set
bridge-to-notation =
  L.suc (L.suc (R2.Rt AL.hΩω)) ≼ VN.rd (W.suc N.G₁.U)

target-from-bridge : bridge-to-notation → yiut-two-above-current
target-from-bridge b =
  ≼-trans b (≼-trans (VN.rd-mono VN.output-lower)
                     (VN.rd→r (proj₁ UT.output)))
```
