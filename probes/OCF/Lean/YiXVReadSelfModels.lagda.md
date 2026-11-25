# YiXVReadSelfModels
> 验收文件。档位：编译定理。在原一层 Ω 上实填自身 ψs 行的全部种子前提。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadSelfModels where
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineNodeModels as M
SrcB = Fold.B₀ (J.ℓ M.r)
χ = Fold.ψs (J.ℓ M.r) (T.εh M.r) (T.ρh M.r) SrcB (J.ℓ M.r) Path.self M.x M.nx
seed : U.UR M.r M.x (W.φ P.here (L.add M.X (λ q → q) M.Ω))
seed = B.weak M.r M.hx (Phi.Frame.mono P.here (Add.right {σ = λ q → q} M.gx A.oneΩ))
```
