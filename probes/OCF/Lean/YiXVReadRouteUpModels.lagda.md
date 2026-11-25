# YiXVReadRouteUpModels
> 验收文件。档位：编译定理。实填一层 Ω 首分支提升的父输出、孩子世界与孩子完整输出。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteUpModels where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadRouteWorldInput as W
import OCF.Lean.YiXVReadRouteRules as Rules
import OCF.Lean.YiXVReadRouteChild as Child
import OCF.Lean.YiXVReadRouteGround as Ground
r : S.Tr S.zero
r = S.suc S.zero
SrcB = Fold.B₀ (J.ℓ r)
Z = Old.seed r
X = L.Ω (L.suc L.zero)
Y : L.Ordᶜ L.zero
Y = L.suc L.zero
gx : A.Gd X
gx = A.oneΩ
gy : A.Gd Y
gy = A.Layer.gs A.Layer.gz
hx : U.UR r S.zero X
hx = B.zero r
hy : U.UR S.zero (S.suc S.zero) Y
hy = ≼-refl _
prefix : W.Out r r P.here SrcB Z S.zero X
prefix = Rules.actual
ChildB = Fold.dS S.zero (T.εh r) (T.ρh r) SrcB S.zero
child-world : W.World r S.zero (P.below P.root) ChildB (O.cap P.here Z X)
child-world = Child.suc P.here SrcB Z prefix
lower : W.Out r S.zero (P.below P.root) ChildB (O.cap P.here Z X) (S.suc S.zero) Y
lower = Ground.upper (P.below P.root) ChildB (O.cap P.here Z X) child-world hy
```
