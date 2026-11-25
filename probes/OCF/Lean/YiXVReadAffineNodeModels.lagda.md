# YiXVReadAffineNodeModels
> 验收文件。档位：编译定理。在原一层 Ω 构造上，实填向上提升节点行的全部分支归纳前提。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineNodeModels where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Align.Level as L
open import OCF.Align.Value using (s≼s)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as Frame
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadAssoc as Assoc
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineGround as Ground
r : S.Tr S.zero
r = S.suc S.zero
Ω = L.Ω (L.suc L.zero)
X = W.seed r
gx : A.Gd X
gx = W.seed-good r
x = O.Ωt (J.ℓ r)
nx = O.Ωt-nz (J.ℓ r)
hx : U.UR r x (W.φ P.here X)
hx = W.World.slots (Start.initial r) r P.here Path.self
σ₀ : L.Simᴵ L.zero (L.suc L.zero)
σ₀ q = L.suc q
g : S.Tr S.zero → S.Tr (J.ℓ r)
g a = S.up S.zero tt (S.suc a) (O.z◃s a)
f : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
f Y = L.add Ω σ₀ Y
good : A.Gd (L.limᵢ L.zero f)
good = Add.good {σ = λ q → q} A.oneΩ A.oneΩ
sim : U.UR r (S.Ω (inj₁ tt) g) (L.limᵢ L.zero f)
sim = B.actual
module C = Phi.Frame {root = r} P.here
IH : ∀ a V Y → A.Gd V → A.Gd Y → A.Le (L.Ω L.zero) Y → U.UR S.zero a V → A.Le (L.suc V) Y →
  U.UR r (O.Up (J.ℓ r) O.stop x nx (g a)) (C.φ (L.add X (λ q → q) (f Y)))
IH a V Y gv gy o ha t = B.weak r
  (Ground.Ground.bound P.here (Down.down-suc Down.here) nx gx hx σ₀ (s≼s ha))
  (C.mono (A.Layer.trans (L.suc L.zero) A.Gd< A.Le< (Add.mono {σ = σ₀} gx t)
    (A.Layer.trans (L.suc L.zero) A.Gd< A.Le<
      (Frame.frame {σ = σ₀} {τ = σ₀} (Add.right {σ = λ q → q} gx A.oneΩ) gy)
      (Assoc.bound {σ = λ q → q} {τ = σ₀} gx A.oneΩ gy))))
```
