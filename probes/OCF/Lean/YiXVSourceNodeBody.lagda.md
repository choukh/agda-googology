# YiXVSourceNodeBody
> 验收文件。档位：编译定理。节点体的源证书与世界输出接口；标准 Ω₁ 的全部前提已填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeBody where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceWorldRules as Rules
import OCF.Lean.YiXVSourceWorldSelf as Self
import OCF.Lean.YiXVSourceWorldUp as Up
import OCF.Lean.YiXVSourceNodeGrowth as Growth

module Node {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (i : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n i)) (L.<→◃ (J.q n i)) → I.T (suc n)) where
  module D = U.Layer n (U.UR n)
  m = I.rank n i
  record Body : Set where
    field
      u : ∀ a X Y → A.Gd m X → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y →
        U.UR n i a X → A.Le m (L.suc X) Y → D.U (g (J.inB n i a)) (f (L.into (L.<→◃ (J.q n i)) Y))
      out : ∀ a X Y → A.Gd m X → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y →
        U.UR n i a X → A.Le m (L.suc X) Y → W.Out (suc n) H p SrcB Z (g (J.inB n i a)) (f (L.into (L.<→◃ (J.q n i)) Y))

module Model₀ where
  p : P.Path 2 1
  p = P.down P.top
  SrcB = Fold.B₀ (J.nat 1)
  Z = L.Ω (L.natᴵ 2)
  Ω = L.Ω (L.natᴵ 1)
  world = W.model 1 2 p
  module Native = Growth.At.Model 0
  g : J.Tr 0 → J.Tr 1
  g a = S.up S.zero tt (S.suc a) (O.z◃s a)
  module N = Node p SrcB Z world F.zero g Native.f
  module D = U.Layer 0 (U.UR 0)
  module R = Rules.Rules p SrcB Z world
  prefix = R.zero-out
  Bchild = Fold.dS (J.nat 0) (Model.ev 1) (Model.rt 1) SrcB S.zero
  Zchild = L.add Z (P.σ p) Ω
  childWorld = Rules.child p SrcB Z world A.actual₁ prefix
  module Root = Self.Base (P.down p) Bchild Zchild childWorld
  body : N.Body
  N.Body.u body a X Y gx gy o ha t = D.uw (D.uu A.actual₁ D.uz tt (UB.sucU 0 ha))
    (Add.mono 1 0 {X = Ω} {X′ = Ω} (B.rfl 1 F.zero {X = Ω} A.actual₁) (λ q → L.suc q) (L.suc X) Y t)
  N.Body.out body a X Y gx gy o ha t = Up.Up.result p SrcB Z world A.actual₁ D.uz gy lowerU prefix (Root.result lowerU)
    where
    lowerU = ≼-trans (UB.sucU 0 ha) t
```
