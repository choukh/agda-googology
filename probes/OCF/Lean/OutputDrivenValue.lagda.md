# 同一输出驱动闭项的两项值包含

本篇只给可核查的包含，不给 EBO 下界：
一是每轮每槽的实际输出被下一轮的合法反馈坐标覆盖；
二是每个完整高源下降输出都被无参数最终闭项包含。
前者是带合法坐标域的高层 `Cover`，后者是可数树的原 `≤ᵛ`；
不将两种关系混为同一种高层序，也不将它们穿过任意折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenValue where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdRichLegValueLegal as Val
import OCF.Lean.ThirdRichLegValueRun as Raw
import OCF.Lean.ThirdRichWorldSections as Frames
import OCF.Lean.OutputDrivenWorld as World
import OCF.Lean.OutputDrivenClosed as C
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)

module Slot (n : ℕ) (u : Wd (Sb n)) (lu : LgW (Sb n) u) where
  module D = World.Driven n u lu
  module F = Frames.Frames n u lu
  output-covered : ∀ s m → Val.Domain.Cover (Tw (Sb n) m) (Raw.LegalT n m)
    (D.output s m) (F.feedback (D.bounds s) (D.output s) m)
  output-covered s m = F.covers (D.bounds s) (D.output s) m

right : ∀ (a b : Cd) → b ≤ᵛ (a ⊞ b)
right a hz = z≤
right a (hs b) = s≤s (right a b)
right a (hl f) = l≤ (λ n → ≤l n (right a (f n)))
right a (hΩ () g)

stage-in-closed : ∀ r → C.stage r ≤ᵛ C.closed
stage-in-closed r = ≤l (suc r) (right (C.y r) (C.stage r))

whole-family : hl C.stage ≤ᵛ C.closed
whole-family = l≤ stage-in-closed
```

`whole-family` 量化全部实际底和完整下降输出，不是前几项测试。
它尚未比较这些输出与 EBO 参照树；`Er`、旧跨底规则及原高层回灌
可能带来的值损失仍是下一值验收的实质问题。
