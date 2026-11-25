# YiXVReadAffineLift
> 验收文件。档位：编译定理。实际读回层号上，原 Up 的完整仿射模拟保持，含自然极限闭实例。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineLift where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadOmega as Ω
import OCF.Lean.YiXVReadOmegaInput as ΩInput
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineGround as Ground
import OCF.Lean.YiXVReadAffineLiftInput as Input
import OCF.Lean.YiXVReadAffineLiftStage as Stage

module Lift {root top} (within : top P.≤ᵀ root) where
  module C = Phi.Frame within
  module I = Input.Frame within
  mutual
    lift : ∀ cur (d : Down.Down top cur) {x X a Y} (nx : J.ℓ top S.⊢ S.zero ◃ x) →
      A.Gd X → U.UR top x (C.φ X) → A.Gd Y → U.UR cur a Y →
      U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx a) (C.φ (L.add X (I.σ d) Y))
    lift S.zero d nx gx hx gy ha = Ground.Ground.bound within d nx gx hx (I.σ d) ha
    lift (S.suc r) d nx gx hx gy ha = Stage.Stage.lift within (S.suc r) (lower (S.suc r)) d nx gx hx gy ha
    lift (S.lim f a) d nx gx hx gy ha = Stage.Stage.lift within (S.lim f a) (lower (S.lim f a)) d nx gx hx gy ha
    lift (S.Ω () g) d nx gx hx gy ha
    lift (S.up r () y ny) d nx gx hx gy ha
    lower : ∀ cur → I.Lower cur
    lower S.zero = I.zero
    lower (S.suc r) d {x} {X} {a} {Y} nx gx hx tt {b} {Z} {nb} gy ha gZ hZ =
      subst (λ (σ : L.Simᴵ (T.lvl r) (T.lvl root)) → U.UR top (O.Up (J.ℓ (S.suc r)) (Down.src d) x nx (S.up a tt b nb))
        (C.φ (L.add (L.add X (I.σ d) Y) σ Z))) (I.σ-child (S.suc r) d tt)
        (lift r (Down.down-suc d) {x = O.Up (J.ℓ (S.suc r)) (Down.src d) x nx a}
          {X = L.add X (I.σ d) Y} {a = b} {Y = Z}
          (O.Up-nz (J.ℓ (S.suc r)) (Down.src d) x nx a) (Add.good {σ = I.σ d} gx gy) ha gZ hZ)
    lower (S.lim f e) d {x} {X} {a} {Y} nx gx hx n {b} {Z} {nb} gy ha gZ hZ =
      subst (λ (σ : L.Simᴵ (T.lvl (f n)) (T.lvl root)) → U.UR top (O.Up (J.ℓ (S.lim f e)) (Down.src d) x nx (S.up a n b nb))
        (C.φ (L.add (L.add X (I.σ d) Y) σ Z))) (I.σ-child (S.lim f e) d n)
        (lift (f n) (Down.down-lim d n) {x = O.Up (J.ℓ (S.lim f e)) (Down.src d) x nx a}
          {X = L.add X (I.σ d) Y} {a = b} {Y = Z}
          (O.Up-nz (J.ℓ (S.lim f e)) (Down.src d) x nx a) (Add.good {σ = I.σ d} gx gy) ha gZ hZ)
    lower (S.Ω () g)
    lower (S.up r () y ny)

actual : ∀ r → U.UR r (O.Up (J.ℓ r) O.stop (O.Ωt (J.ℓ r)) (O.Ωt-nz (J.ℓ r)) (O.Ωt (J.ℓ r)))
  (W.φ P.here (L.add (W.seed r) (λ q → q) (Ω.cap r)))
actual r = Lift.lift {root = r} {top = r} P.here r Down.here (O.Ωt-nz (J.ℓ r))
  (W.seed-good r) (W.World.slots (Start.initial r) r P.here Path.self) (Ω.good r) (Ω.cover r)
actual-ω : U.UR ΩInput.ω
  (O.Up (J.ℓ ΩInput.ω) O.stop (O.Ωt (J.ℓ ΩInput.ω)) (O.Ωt-nz (J.ℓ ΩInput.ω)) (O.Ωt (J.ℓ ΩInput.ω)))
  (W.φ P.here (L.add (W.seed ΩInput.ω) (λ q → q) (Ω.cap ΩInput.ω)))
actual-ω = actual ΩInput.ω

lift-child : ∀ {root} top (within : top P.≤ᵀ root) (c : S.Ch (J.ℓ top))
  {x X b Y} (nx : J.ℓ top S.⊢ S.zero ◃ x) → A.Gd X → U.UR top x (W.φ within X) →
  A.Gd Y → U.Fam top (J.child-slot top c) (J.ctoB top c b) Y →
  U.UR top (O.Upc (J.ℓ top) c x nx b)
    (W.φ within (L.add X (λ q → Out.σ within (J.σchild top c q)) Y))
lift-child S.zero within () nx gx hx gy hy
lift-child (S.suc r) within tt nx gx hx gy hy =
  Lift.lift within r (Down.down-suc Down.here) nx gx hx gy hy
lift-child (S.lim f a) within n nx gx hx gy hy =
  Lift.lift within (f n) (Down.down-lim Down.here n) nx gx hx gy hy
lift-child (S.Ω () g) within c nx gx hx gy hy
lift-child (S.up r () y ny) within c nx gx hx gy hy
```
