# YiXVReadRouteGround
> 验收文件。档位：编译定理。零源层的 Route 世界提升为旧全路径世界，复用原零层完整输出。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteGround where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadGround as Ground
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteWorldInput as W
ground : ∀ {root within SrcB Z} → W.World root S.zero within SrcB Z → Old.World root S.zero within SrcB Z
Old.World.good (ground w) = W.World.good w
Old.World.bot (ground w) = W.World.bot w
Old.World.slots (ground w) S.zero p Path.self = W.World.slots w S.zero p Path.self R.here
Old.World.slots (ground w) (S.suc y) p ()
Old.World.slots (ground w) (S.lim f d) p ()
Old.World.slots (ground w) (S.Ω () g) p v
Old.World.slots (ground w) (S.up r () y ny) p v
upper : ∀ {root} (within : S.zero P.≤ᵀ root) (SrcB : Fold.Base S.zero) Z →
  W.World root S.zero within SrcB Z → ∀ {a X} → U.UR S.zero a X → W.Out root S.zero within SrcB Z a X
upper {root} within SrcB Z w h = W.from-out (Ground.Ground.upper root within SrcB Z (ground w) h)
```
