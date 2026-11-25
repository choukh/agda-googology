# YiXVReadRouteOwn
> 验收文件。档位：编译定理。Route 世界提供自身槽位种子，接入 ReadSelf 的 Layer.U 保持接口。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteOwn where
open import Data.Product using (proj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteWorldInput as W
import OCF.Lean.YiXVReadSelf as Self
module Own {root} (cur : S.Tr S.zero) (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (w : W.World root cur within SrcB Z) where
  γ = Fold.bs SrcB (J.ℓ cur) Path.self
  nγ = Fold.ns SrcB (J.ℓ cur) Path.self
  seed : U.UR cur γ (Old.φ within (L.add Z (O.σ within) (L.Ω (T.lvl cur))))
  seed = B.weak cur (W.World.slots w cur within Path.self R.here)
    (Phi.Frame.mono within (Add.right {σ = O.σ within} (W.World.good w) (proj₁ (Ω.model (T.lvl cur)))))
  module Run = Self.Self cur within SrcB Z (W.World.good w) γ nγ seed
```
