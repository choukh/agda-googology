# YiXVReadEmbedLiftInput
> 验收文件。档位：编译定理。Route 的参照嵌入，一层与自然极限上的嵌入提升前提先实填。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadEmbedLiftInput where
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadAffineLift as Lift
import OCF.Lean.YiXVReadOmegaInput as Ω
import OCF.Lean.YiXVRefLift as Ref
import OCF.Lean.YiXVReadEmbedInput as E

σ : ∀ {cur orig v} → R.Route cur orig v → L.Simᴵ (T.lvl orig) (T.lvl cur)
σ R.here q = q
σ (R.ins {r = r} rv) q = J.σchild (S.suc r) tt (σ rv q)
σ (R.inl {f = f} {d = d} n rv) q = J.σchild (S.lim f d) n (σ rv q)
σ (R.inlu {f = f} {d = d} rv) q = J.σchild (S.lim f d) 0 (σ (rv 0) q)

module M₁ where
  r : S.Tr S.zero
  r = S.suc S.zero
  x = O.Ωt (J.ℓ r)
  nx = O.Ωt-nz (J.ℓ r)
  X = W.seed r
  Y : L.Ordᶜ L.zero
  Y = L.suc L.zero
  gy : A.Gd Y
  gy = A.Layer.gs A.Layer.gz
  hy : U.UR S.zero (proj₁ E.one) Y
  hy = ≼-refl Y
  result : U.UR r (O.Up (J.ℓ r) O.stop x nx (proj₁ (E.emb R.model₁ E.one)))
    (W.φ P.here (L.add X (λ q → q) (Ref.embedded (σ R.model₁) Y)))
  result = Lift.Lift.lift P.here S.zero (Down.down-suc Down.here) nx
    (W.seed-good r) (W.World.slots (Start.initial r) r P.here Path.self) gy hy

module Mω where
  r = Ω.ω
  x = O.Ωt (J.ℓ r)
  nx = O.Ωt-nz (J.ℓ r)
  X = W.seed r
  result : U.UR r (O.Up (J.ℓ r) O.stop x nx (proj₁ (E.emb R.model-ω E.one)))
    (W.φ P.here (L.add X (λ q → q) (Ref.embedded (σ R.model-ω) M₁.Y)))
  result = Lift.Lift.lift P.here S.zero (Down.down-lim Down.here 0) nx
    (W.seed-good r) (W.World.slots (Start.initial r) r P.here Path.self) M₁.gy M₁.hy
```
