# YiXVSourceWorldNode
> 验收文件。档位：编译定理。保留／对角分派合成全部节点世界输出；标准 Ω₁ 实例已填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldNode where
open import Data.Nat using (ℕ; zero; suc; z≤n)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (s0; ss)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceNodeBody as Body
import OCF.Lean.YiXVSourceNodeDiag as Diag
import OCF.Lean.YiXVSourceNodeKeep as Keep

module Node {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (i : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n i)) (L.<→◃ (J.q n i)) → I.T (suc n))
  (law : A.Layer.SC n (A.GoFam n) (A.LeFam n) (J.q n i) f)
  (gb : ∀ u → A.Layer.GU n (A.GoFam n) (A.LeFam n) (J.q n i) u →
    A.Layer.Floor n (A.GoFam n) (A.LeFam n) (J.q n i) u → A.Gd (suc n) (f u))
  (body : Body.Node.Body p SrcB Z world i g f) where
  module Src = U.Layer n (U.UR n)
  module D = Diag.Node p SrcB Z world i g f law gb body
  certificate : U.U (suc n) (S.Ω (J.slot n i) g) (L.limᵢ (J.q n i) f)
  certificate = Src.un i (Body.Node.Body.u body)
  result : W.Out (suc n) H p SrcB Z (S.Ω (J.slot n i) g) (L.limᵢ (J.q n i) f)
  W.Out.bot result = D.bot
  W.Out.slots result zero s = Slots.kcase₀ s i (Default.ev (suc n)) (Default.rt (suc n))
    (λ x → U.U 0 x (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))) (T.result z≤n)
    where module T = D.Target 0 s
  W.Out.slots result (suc j) s = Slots.kcase₊ s i (Default.ev (suc n)) (Default.rt (suc n))
    (λ x → U.U (suc j) x (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f))))
    T.result (λ k cv e br → Keep.Keep.result p SrcB Z world i g f body s k cv e br)
    where module T = D.Target (suc j) s

module Model = Node Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z Body.Model₀.world F.zero Body.Model₀.g Body.Model₀.Native.f
  Body.Model₀.Native.law Body.Model₀.Native.body Body.Model₀.body
actual : W.Out 1 2 Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z (O.Ωt (J.nat 1))
  (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1))
actual = Model.result
```
