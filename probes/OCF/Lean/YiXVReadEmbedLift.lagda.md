# YiXVReadEmbedLift
> 验收文件。档位：编译定理。原 Up 经跨分支嵌入后仍有仿射读回模拟，复用既有提升保持。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadEmbedLift where
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAddFrame as Frame
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAssoc as Assoc
import OCF.Lean.YiXVReadAffineLiftInput as Input
import OCF.Lean.YiXVReadAffineLift as Lift
import OCF.Lean.YiXVRefLift as Ref
import OCF.Lean.YiXVReadEmbedInput as E
import OCF.Lean.YiXVReadEmbed as Emb
import OCF.Lean.YiXVReadEmbedLiftInput as M

module Bound {root top} (within : top P.≤ᵀ root) where
  module I = Input.Frame within
  module N = A.Layer (T.lvl root) A.Gd< A.Le<
  forward : ∀ {cur orig v} (d : Down.Down top cur) (rv : R.Route cur orig v)
    {X Y} → A.Gd X → A.Gd Y →
    A.Le (L.add X (I.σ (Emb.follow d rv)) Y)
      (L.add X (I.σ d) (Ref.embedded (M.σ rv) Y))
  forward d rv gx gy = N.trans
    (Frame.frame {σ = I.σ (Emb.follow d rv)} {τ = λ q → I.σ d (M.σ rv q)} (N.rfl gx) gy)
    (Assoc.bound {σ = I.σ d} {τ = M.σ rv} gx A.Layer.gz gy)
  result : ∀ {cur orig v} (d : Down.Down top cur) (rv : R.Route cur orig v)
    {x X} (nx : J.ℓ top S.⊢ S.zero ◃ x) (z : E.NZ (J.ℓ orig)) {Y} →
    A.Gd X → U.UR top x (W.φ within X) → A.Gd Y → U.UR orig (proj₁ z) Y →
    U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx (proj₁ (E.emb rv z)))
      (W.φ within (L.add X (I.σ d) (Ref.embedded (M.σ rv) Y)))
  result {orig = orig} d rv {x} {X} nx z {Y} gx hx gy hy = B.weak top
    (subst (λ a → U.UR top a (W.φ within (L.add X (I.σ (Emb.follow d rv)) Y)))
      (sym (Emb.up d rv x nx z))
      (Lift.Lift.lift within orig (Emb.follow d rv) nx gx hx gy hy))
    (Phi.Frame.mono within (forward d rv gx gy))
```
