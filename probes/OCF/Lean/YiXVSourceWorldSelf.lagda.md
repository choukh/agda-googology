# YiXVSourceWorldSelf
> 验收文件。档位：编译定理。同层槽位的仿射模拟与第 0 层世界语义。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldSelf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (s0)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVSourceAffineSelf as Self
import OCF.Lean.YiXVSourceWorldGround as Ground
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVSourceWorldInput as W

module Same {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) where
  γ = Fold.bs SrcB (J.nat (suc n)) (Slots.pth s0)
  nγ = Fold.ns SrcB (J.nat (suc n)) (Slots.pth s0)
  seed : U.U (suc n) γ (W.φ p s0 (L.add Z (P.σ p) (L.Ω (L.natᴵ (suc n)))))
  seed = UB.weakU (suc n) (W.World.slots world (suc n) s0)
    (W.φ-mix p s0 p s0 (Right.right H (suc n) (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p)
      (L.Ω (L.natᴵ (suc n))) (proj₁ (B.Ω-model (suc n) F.zero))))
  module Run = Self.Self n H (W.pc p s0) (λ q → L.suc q) (P.σ p) SrcB Z (W.World.good world) γ nγ seed
  result : ∀ {x X} → A.Gd (suc n) X → U.U (suc n) x X →
    U.U (suc n) (Fold.ψs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (J.nat (suc n))
      (Slots.pth s0) γ nγ x) (W.φ p s0 (L.add Z (P.σ p) X))
  result = Run.result

module Base {H} (p : P.Path H zero) (SrcB : Fold.Base S.zero) (Z : I.T H) (world : W.World 0 H p SrcB Z) where
  module G = Ground.World H Z (W.World.good world) (P.σ p) SrcB (W.World.bot world)
    (≼-trans (W.World.slots world zero s0) (proj₁ (ZR.approx (W.pc p s0) (λ q → L.suc q) Z)))
  result : ∀ {x X} → U.U 0 x X → W.Out 0 H p SrcB Z x X
  W.Out.bot (result h) = proj₁ (G.upper h)
  W.Out.slots (result {X = X} h) .zero s0 = ≼-trans (proj₂ (G.upper h))
    (proj₂ (ZR.approx (W.pc p s0) (λ q → L.suc q) (L.add Z (P.σ p) X)))
```
