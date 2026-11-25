# YiXVReadRouteNodeModels
> 验收文件。档位：编译定理。规范一层 Ω 的全部分支完整 Route 输出前提先实填。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteNodeModels where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (s≼s; ≼-trans)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadAffineNodeModels as N
import OCF.Lean.YiXVReadRouteWorldInput as W
import OCF.Lean.YiXVReadRouteRules as Rules
import OCF.Lean.YiXVReadRouteChild as Child
import OCF.Lean.YiXVReadRouteGround as Ground
import OCF.Lean.YiXVReadRouteUpSuc as Up
r = N.r
SrcB = Fold.B₀ (J.ℓ r)
Z = Old.seed r
module Ops = Rules.Rules P.here SrcB Z W.model₁
module Lift = Up.Up S.zero P.here SrcB Z W.model₁
prefix : W.Out r r P.here SrcB Z S.zero N.Ω
prefix = Ops.zero
child : S.zero P.≤ᵀ r
child = P.below P.root
ChildB = Fold.dS (J.ℓ S.zero) (T.εh r) (T.ρh r) SrcB S.zero
world : W.World r S.zero child ChildB (Out.cap P.here Z N.Ω)
world = Child.suc P.here SrcB Z prefix
body : ∀ a V Y → A.Gd V → A.Gd Y → A.Le (L.Ω L.zero) Y →
  U.Fam r (inj₁ tt) a V → A.Le (L.suc V) Y →
  W.Out r r P.here SrcB Z (N.g a) (N.f Y)
body a V Y gv gy o ha t = Lift.result A.oneΩ (B.zero r) gy
  (≼-trans (s≼s ha) (G.value t)) prefix
  (Ground.upper child ChildB (Out.cap P.here Z N.Ω) world (≼-trans (s≼s ha) (G.value t)))
```
