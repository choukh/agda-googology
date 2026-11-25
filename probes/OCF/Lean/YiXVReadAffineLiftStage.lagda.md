# YiXVReadAffineLiftStage
> 验收文件。档位：编译定理。固定实际源层时，按源模拟递归合成原 Up 的全部行。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineLiftStage where
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadNext as Next
import OCF.Lean.YiXVReadAssoc as Assoc
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineLiftInput as Input
import OCF.Lean.YiXVReadAffineNode as Node
import OCF.Lean.YiXVReadAffineNodeModels as Model

module Stage {root top} (within : top P.≤ᵀ root) (cur : S.Tr S.zero)
  (low : Input.Frame.Lower within cur) where
  module C = Phi.Frame within
  module I = Input.Frame within
  module D = U.Layer cur (U.Fam cur)
  module R = A.Layer (T.lvl cur) A.Gd< A.Le<
  lift : ∀ (d : Down.Down top cur) {x X a Y} (nx : J.ℓ top S.⊢ S.zero ◃ x) →
    A.Gd X → U.UR top x (C.φ X) → A.Gd Y → D.U a Y →
    U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx a) (C.φ (L.add X (I.σ d) Y))
  lift d nx gx hx gy D.uz = B.weak top hx
    (C.mono (Add.right {σ = I.σ d} gx (proj₁ (Ω.model (T.lvl cur)))))
  lift d {a = S.suc a} nx gx hx (R.gs gy) (D.us ha) = Next.next top
    (O.Up-nz (J.ℓ cur) (Down.src d) _ nx a) (C.good (Add.good gx gy)) (lift d nx gx hx gy ha)
  lift d nx gx hx gy (D.uw ha t) = B.weak top (lift d nx gx hx (R.left t) ha)
    (C.mono (Add.mono {σ = I.σ d} gx t))
  lift d nx gx hx gy (D.ul h) = B.limU top (λ n → lift d nx gx hx gy (h n))
  lift d {x} {X} nx gx hx gy@(R.gn ex law gb) (D.un p {g} {f} h) =
    Node.Node.Run.result within d p x nx X (I.σ d) gx g f gy
      (λ a V Y gv gY o ha t → lift d nx gx hx
        (gb Y (A.good-in (L.<→◃ (J.q cur p)) gY) (A.le-in (L.<→◃ (J.q cur p)) o))
        (h a V Y gv gY o ha t))
  lift d {x} {X} nx gx hx gy (D.uu c {a = a} {b = b} {nb = nb} {X = Y} {Y = Z} gy₀ hy gZ hZ) =
    B.weak top (low d {x = x} {X = X} {a = a} {Y = Y} nx gx hx c {b = b} {Z = Z} {nb = nb}
      gy₀ (lift d nx gx hx gy₀ hy) gZ hZ)
      (C.mono (Assoc.bound {σ = I.σ d} {τ = J.σchild cur c} gx gy₀ gZ))

module MI = Input.Frame {root = Model.r} {top = Model.r} P.here
module M = Stage {root = Model.r} {top = Model.r} P.here Model.r MI.one
actual : U.UR Model.r (O.Up (J.ℓ Model.r) O.stop Model.x Model.nx (S.Ω _ Model.g))
  (W.φ P.here (L.add Model.X (λ q → q) (L.limᵢ L.zero Model.f)))
actual = M.lift Down.here Model.nx Model.gx Model.hx Model.good Model.sim
```
