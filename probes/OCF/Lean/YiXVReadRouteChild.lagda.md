# YiXVReadRouteChild
> 验收文件。档位：编译定理。Route 证据经原 ins/inl 延伸，保持 dS/dL 孩子世界的所有字段。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteChild where
open import Data.Nat using (ℕ)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadCoordinates as C
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteWorldInput as W
suc : ∀ {root r} (within : S.suc r P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ (S.suc r))) Z {a X} →
  W.Out root (S.suc r) within SrcB Z a X →
  W.World root r (C.inside P.root within)
    (Fold.dS (J.ℓ r) (T.εh (S.suc r)) (T.ρh (S.suc r)) SrcB a) (O.cap within Z X)
W.World.good (suc within SrcB Z h) = W.Out.good h
W.World.bot (suc within SrcB Z h) = W.Out.bot h
W.World.slots (suc within SrcB Z h) y p v rv = W.Out.slots h y p (Path.ins v) (R.ins rv)
lim : ∀ {root f d} (within : S.lim f d P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ (S.lim f d))) Z (n : ℕ) {a X} →
  W.Out root (S.lim f d) within SrcB Z a X →
  W.World root (f n) (C.inside (P.branch n) within)
    (Fold.dL (λ k → J.ℓ (f k)) (T.εh (S.lim f d)) (T.ρh (S.lim f d)) SrcB n a) (O.cap within Z X)
W.World.good (lim within SrcB Z n h) = W.Out.good h
W.World.bot (lim within SrcB Z n h) = W.Out.bot h
W.World.slots (lim within SrcB Z n h) y p v rv = W.Out.slots h y p (Path.inl n v) (R.inl n rv)
```
