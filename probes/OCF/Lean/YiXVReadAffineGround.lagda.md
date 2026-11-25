# YiXVReadAffineGround
> 验收文件。档位：编译定理。全局实际上界内，原 Up 从零源层向上提升的仿射模拟。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineGround where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼l)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadNext as Next
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVFlatInput as Flat
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi

module Model where
  r : S.Tr S.zero
  r = S.suc S.zero
  p : r P.≤ᵀ r
  p = P.here
  d : Down.Down r S.zero
  d = Down.down-suc Down.here
  X = W.seed r
  gx : A.Gd X
  gx = W.seed-good r
  x = O.Ωt (J.ℓ r)
  nx = O.Ωt-nz (J.ℓ r)
  hx : U.UR r x (W.φ p X)
  hx = W.World.slots (Start.initial r) r p Path.self
  hy : U.UR S.zero (O.Ωt S.zero) (L.suc L.zero)
  hy = ≼-refl _

module Ground {root r} (p : r P.≤ᵀ root) where
  module C = Phi.Frame p
  exact : ∀ {x X} (d : Down.Down r S.zero) (nx : J.ℓ r S.⊢ S.zero ◃ x) →
    A.Gd X → U.UR r x (C.φ X) → (σ : L.Simᴵ L.zero (T.lvl root)) (z : S.Tr S.zero) →
    U.UR r (O.Up S.zero (Down.src d) x nx z) (C.φ (L.add X σ (Read.read z)))
  exact d nx gx hx σ S.zero = hx
  exact {X = X} d nx gx hx σ (S.suc z) = Next.next r
    (O.Up-nz S.zero (Down.src d) _ nx z)
    (C.good (Add.good gx (G.good (Read.read z)))) (exact d nx gx hx σ z)
  exact {X = X} d nx gx hx σ (S.lim f a) = B.limU r (λ n → B.weak r
    (exact d nx gx hx σ (f n)) (C.mono (Add.mono {σ = σ} gx
      (G.native (≼l n (≼-refl (Read.read (f n))))))))
  exact d nx gx hx σ (S.Ω () f)
  exact d nx gx hx σ (S.up z () y ny)
  bound : ∀ {x X z Y} (d : Down.Down r S.zero) (nx : J.ℓ r S.⊢ S.zero ◃ x) →
    A.Gd X → U.UR r x (C.φ X) → (σ : L.Simᴵ L.zero (T.lvl root)) → U.UR S.zero z Y →
    U.UR r (O.Up S.zero (Down.src d) x nx z) (C.φ (L.add X σ Y))
  bound {z = z} d nx gx hx σ hy = B.weak r (exact d nx gx hx σ z)
    (C.mono (Add.mono {σ = σ} gx (G.native hy)))

actual : U.UR Model.r (O.Up S.zero (Down.src Model.d) Model.x Model.nx (O.Ωt S.zero))
  (W.φ Model.p (L.add Model.X (Flat.empty (T.lvl Model.r)) (L.suc L.zero)))
actual = Ground.bound Model.p Model.d Model.nx Model.gx Model.hx
  (Flat.empty (T.lvl Model.r)) Model.hy
```
