# YiXVReadSelf
> 验收文件。档位：编译定理。原自身 ψs 的仿射模拟，输入为当前层的 Layer.U 证书；不声称零层普通值模拟版本。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadSelf where
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadNext as Next
import OCF.Lean.YiXVReadAssoc as Assoc
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineLift as Lift
import OCF.Lean.YiXVReadAffineNode as Node
import OCF.Lean.YiXVReadAffineNodeModels as M
import OCF.Lean.YiXVReadSelfModels as Model

module Self {root} (cur : S.Tr S.zero) (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (gz : A.Gd Z) (γ : S.Tr (J.ℓ cur)) (nγ : J.ℓ cur S.⊢ S.zero ◃ γ)
  (seed : U.UR cur γ (W.φ within (L.add Z (Out.σ within) (L.Ω (T.lvl cur))))) where
  module C = Phi.Frame within
  module D = U.Layer cur (U.Fam cur)
  module R = A.Layer (T.lvl cur) A.Gd< A.Le<
  χ = Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ cur) Path.self γ nγ
  nχ = Fold.nzs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ cur) Path.self γ nγ
  result : ∀ {a Y} → A.Gd Y → D.U a Y → U.UR cur (χ a) (C.φ (L.add Z (Out.σ within) Y))
  result gy D.uz = seed
  result (R.gs gy) (D.us {a = a} ha) = Next.next cur (nχ a)
    (C.good (Add.good {σ = Out.σ within} gz gy)) (result gy ha)
  result gy (D.uw ha t) = B.weak cur (result (R.left t) ha)
    (C.mono (Add.mono {σ = Out.σ within} gz t))
  result gy (D.ul h) = B.limU cur (λ n → result gy (h n))
  result gy@(R.gn ex law gb) (D.un p {g} {f} h) =
    Node.Node.General.result within Down.here p γ nγ Z (Out.σ within) gz g f gy χ refl
      (λ a V Y gv gY o ha t → result
        (gb Y (A.good-in (L.<→◃ (J.q cur p)) gY) (A.le-in (L.<→◃ (J.q cur p)) o))
        (h a V Y gv gY o ha t))
  result gy (D.uu c {a = a} {b = b} {nb = nb} {X = Y} {Y = X} gy₀ hy gx hx) = B.weak cur
    (Lift.lift-child cur within c (nχ a) (Add.good {σ = Out.σ within} gz gy₀) (result gy₀ hy) gx hx)
    (C.mono (Assoc.bound {σ = Out.σ within} {τ = J.σchild cur c} gz gy₀ gx))

module Actual = Self M.r P.here Model.SrcB M.X M.gx M.x M.nx Model.seed
actual : U.UR M.r (Model.χ (S.Ω _ M.g))
  (W.φ P.here (L.add M.X (λ q → q) (L.limᵢ L.zero M.f)))
actual = Actual.result M.good M.sim
```
