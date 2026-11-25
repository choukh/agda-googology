# YiXVReadRouteUpSuc
> 验收文件。档位：编译定理。实际后继层提升的完整 Route 世界输出，含原一层 Ω 首分支的闭实例。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteUpSuc where
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as Frame
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadAssoc as Assoc
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadCoordinates as C
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadPhiPaths as Paths
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteWorldInput as W
import OCF.Lean.YiXVReadRouteRules as Rules
import OCF.Lean.YiXVReadRouteOwn as Own
import OCF.Lean.YiXVReadRouteUpModels as M

module Up {root} (r : S.Tr S.zero) (within : S.suc r P.≤ᵀ root)
  (SrcB : Fold.Base (J.ℓ (S.suc r))) (Z : L.Ordᶜ (T.lvl root))
  (w : W.World root (S.suc r) within SrcB Z) where
  cur = S.suc r
  child = C.inside P.root within
  ChildB : S.Tr (J.ℓ cur) → Fold.Base (J.ℓ r)
  ChildB a = Fold.dS (J.ℓ r) (T.εh cur) (T.ρh cur) SrcB a
  module D = U.Layer cur (U.Fam cur)
  module N = A.Layer (T.lvl root) A.Gd< A.Le<
  module Same = Own.Own cur within SrcB Z w
  module Ops = Rules.Rules within SrcB Z w
  forward : ∀ {X Y} → A.Gd X → A.Gd Y →
    A.Le (O.cap child (O.cap within Z X) Y)
      (O.cap within Z (L.add X (J.σchild cur tt) Y))
  forward {X} gx gy = N.trans
    (Frame.frame {σ = O.σ child} {τ = λ q → O.σ within (J.σchild cur tt q)}
      (N.rfl (Add.good {σ = O.σ within} (W.World.good w) gx)) gy)
    (Assoc.bound {σ = O.σ within} {τ = J.σchild cur tt} (W.World.good w) gx gy)
  result : ∀ {a X b Y} {nb : J.ℓ r S.⊢ S.zero ◃ b} → A.Gd X → U.UR cur a X →
    A.Gd Y → U.UR r b Y → W.Out root cur within SrcB Z a X →
    W.Out root r child (ChildB a) (O.cap within Z X) b Y →
    W.Out root cur within SrcB Z (S.up a tt b nb) (L.add X (J.σchild cur tt) Y)
  W.Out.good (result gx hx gy hy prefix lower) =
    Add.good {σ = O.σ within} (W.World.good w) (Add.good {σ = J.σchild cur tt} gx gy)
  W.Out.bot (result gx hx gy hy prefix lower) = ≼-trans (W.Out.bot {cur = r} lower) (Ops.Ref.value-mono (forward gx gy))
  W.Out.slots (result {a = a} {b = b} {nb = nb} gx hx gy hy prefix lower) .cur p .Path.self R.here = B.weak cur
    (Same.Run.result (Add.good {σ = J.σchild cur tt} gx gy) (D.uu tt {a = a} {b = b} {nb = nb} gx hx gy hy))
    (Paths.change within p (Add.good {σ = O.σ within} (W.World.good w) (Add.good {σ = J.σchild cur tt} gx gy)))
  W.Out.slots (result gx hx gy hy prefix lower) y p v (R.ins {v = v′} rv) =
    B.weak y (W.Out.slots {cur = r} lower y p v′ rv) (Phi.Frame.mono p (forward gx gy))

module Actual = Up S.zero P.here M.SrcB M.Z W.model₁
actual : W.Out M.r M.r P.here M.SrcB M.Z (S.up S.zero tt (S.suc S.zero) S.◃s)
  (L.add M.X (J.σchild M.r tt) M.Y)
actual = Actual.result M.gx M.hx M.gy M.hy M.prefix M.lower
```
