# YiXVReadRouteWorldNode
> 验收文件。档位：编译定理。分支完整输出与参照合法性给节点完整 Route 输出，含规范 Ω₁ 实例。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteWorldNode where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadRouteWorldInput as W
import OCF.Lean.YiXVReadRouteKeep as KP
import OCF.Lean.YiXVReadRouteNodeKeep as Keep
import OCF.Lean.YiXVReadRouteNodeDiag as Diag
import OCF.Lean.YiXVReadRouteNodeModels as Models
import OCF.Lean.YiXVReadAffineNodeModels as M

module Node {root cur} (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (w : W.World root cur within SrcB Z)
  (p : S.Pos (J.ℓ cur)) (g : S.Br (J.ℓ cur) p → S.Tr (J.ℓ cur))
  (f : L.U (T.lvl (J.slot cur p)) (L.<→◃ (J.q cur p)) → L.Ordᶜ (T.lvl cur))
  (gnode : A.Gd (L.limᵢ (J.q cur p) f))
  (body : ∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot cur p))) Y →
    U.Fam cur p a X → A.Le (L.suc X) Y →
    W.Out root cur within SrcB Z (g a) (f (L.into (L.<→◃ (J.q cur p)) Y))) where
  module K = Keep.Node within SrcB Z w p g f gnode body
  module D = Diag.Node within SrcB Z w p g f gnode body
  result : W.Out root cur within SrcB Z (S.Ω p g) (L.limᵢ (J.q cur p) f)
  W.Out.good result = Add.good {σ = Out.σ within} (W.World.good w) gnode
  W.Out.bot result = D.bot
  W.Out.slots result y py v rv = KP.kp cur p rv
    (λ pt cv → S.Ω pt (λ a → D.Target.Φ py v rv (g (cv a))))
    (D.Target.default py v rv)
    (λ x → U.UR y x (Old.φ py (Out.cap within Z (L.limᵢ (J.q cur p) f))))
    (λ pt cv link → K.Target.result py v rv pt cv link) (D.Target.result py v rv)

open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
module Actual = Node P.here Models.SrcB Models.Z W.model₁ (inj₁ tt) M.g M.f M.good Models.body
actual : W.Out M.r M.r P.here Models.SrcB Models.Z (S.Ω (inj₁ tt) M.g) (L.limᵢ L.zero M.f)
actual = Actual.result
```
