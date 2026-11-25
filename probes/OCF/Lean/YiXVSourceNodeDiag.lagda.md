# YiXVSourceNodeDiag
> 验收文件。档位：编译定理。节点对角链的底层值与槽位界；实际轨道和部分和均覆盖。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeDiag where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst; subst₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as Fd
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceGrowthInput as GI
import OCF.Lean.YiXVSourceGrowth as Gr
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceOrbit as Orbit
import OCF.Lean.YiXVSourceNodeBody as Body
import OCF.Lean.YiXVSourceNodeGrowth as Growth

module Node {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (i : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n i)) (L.<→◃ (J.q n i)) → I.T (suc n))
  (law : A.Layer.SC n (A.GoFam n) (A.LeFam n) (J.q n i) f)
  (gb : ∀ u → A.Layer.GU n (A.GoFam n) (A.LeFam n) (J.q n i) u →
    A.Layer.Floor n (A.GoFam n) (A.LeFam n) (J.q n i) u → A.Gd (suc n) (f u))
  (body : Body.Node.Body p SrcB Z world i g f) where
  m = I.rank n i
  module Ref = Growth.At.Frame n m H (J.q n i) (P.σ p) Z (W.World.good world) f law gb
  module Env = Ref.Env
  module Orb = Orbit.Orbit n i SrcB g
  high : I.T m → I.T H
  high Y = L.add Z (P.σ p) (f (L.into (L.<→◃ (J.q n i)) Y))
  high-good : ∀ Y → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y → A.Gd H (high Y)
  high-good Y gy o = subst (A.Gd H) (cong (λ z → L.add Z (P.σ p) (f z)) (Ref.ca-eq Y)) (Ref.high-good Y gy o)
  low : ∀ a X → U.U m a X → U.UR n i a X
  low a X h = subst (λ X → X) (sym (UB.stable n i a X)) h

  step : GI.SourceStep m Env.P Orb.step
  GI.SourceStep.step step a X Y gx gy o ha t = subst (U.U m (Orb.step a))
    (sym (cong (λ z → L.ψ Env.qa (λ r → r) (L.add Z (P.σ p) (f z))) (Ref.ca-eq Y)))
    (UB.weakU m
      (W.Out.slots {n = suc n} (Body.Node.Body.out body a X Y gx gy o (low a X ha) t) m (Slots.slot-path n i))
      (Q.Ops.mono (Fd.ops H) m (W.pc p (Slots.slot-path n i)) Env.qa (λ q → L.suc q) (λ r → r)
        (high Y) (high Y) (B.rfl H F.zero {X = high Y} (high-good Y gy o))))
  module Chain = Gr.Chain m Env.P Ref.growth Orb.step step Orb.orbit

  Φ₀ : J.Tr (suc n) → J.Tr zero
  Φ₀ = Fold.ψ⊥ (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB
  F₀ : ℕ → J.Tr zero
  F₀ k = Φ₀ (g (Orb.br k))
  row₀ : ∀ k X Y → A.Gd m X → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y →
    U.U m (Chain.c k) X → A.Le m (L.suc X) Y → U.U zero (F₀ k) (Env.ν₀ Y)
  row₀ k X Y gx gy o ha t = subst₂ (U.U zero) (Orb.row 0 Φ₀ k)
    (sym (cong (λ z → L.ψ⁰ (L.add Z (P.σ p) (f z))) (Ref.ca-eq Y)))
    (W.Out.bot {n = suc n} (Body.Node.Body.out body (Orb.c k) X Y gx gy o (low _ X ha) t))
  module Bot = Chain.Slot 0 Env.ν₀ Ref.output₀ F₀ row₀
  bot : read (Fold.ψ⊥ (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (S.Ω (J.slot n i) g)) ≼
    L.ψ⁰ (L.add Z (P.σ p) (L.limᵢ (J.q n i) f))
  bot = subst (U.U 0 (O.limc F₀ (λ k → Fold.nz⊥ (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (g (Orb.br k)))))
    (sym Env.bot-shape) (Bot.result (λ k → Fold.nz⊥ (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (g (Orb.br k))))

  module Target (j : ℕ) (s : Sbᶠ (suc n) j) where
    module Native = Env.Target j (W.pc p s) (λ q → L.suc q)
    Φ : J.Tr (suc n) → J.Tr j
    Φ x = Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s)
      (Fold.bs SrcB (J.nat j) (Slots.pth s)) (Fold.ns SrcB (J.nat j) (Slots.pth s)) x
    F : ℕ → J.Tr j
    F k = Φ (g (Orb.br k))
    row : ∀ k X Y → A.Gd m X → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y → U.U m (Chain.c k) X → A.Le m (L.suc X) Y → U.U j (F k) (Native.ν Y)
    row k X Y gx gy o ha t = subst₂ (U.U j) (Orb.row j Φ k)
      (sym (cong (λ z → W.φ p s (L.add Z (P.σ p) (f z))) (Ref.ca-eq Y)))
      (W.Out.slots {n = suc n} (Body.Node.Body.out body (Orb.c k) X Y gx gy o (low _ X ha) t) j s)
    module Column = Chain.Slot j Native.ν (Ref.output j (W.pc p s) (λ q → L.suc q)) F row
    nz : ∀ k → J.nat j S.⊢ S.zero ◃ F k
    nz k = Fold.nzs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s)
      (Fold.bs SrcB (J.nat j) (Slots.pth s)) (Fold.ns SrcB (J.nat j) (Slots.pth s)) (g (Orb.br k))
    default = O.limc F nz
    result : j ≤ m → U.U j default (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))
    result le = subst (U.U j default) (sym (Native.diagonal le)) (Column.result nz)

module Model = Node Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z Body.Model₀.world F.zero Body.Model₀.g Body.Model₀.Native.f
  Body.Model₀.Native.law Body.Model₀.Native.body Body.Model₀.body
actual : read (Fold.ψ⊥ (J.nat 1) (Default.ev 1) (Default.rt 1) Body.Model₀.SrcB (O.Ωt (J.nat 1))) ≼
  L.ψ⁰ (L.add Body.Model₀.Z (P.σ Body.Model₀.p) (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1)))
actual = Model.bot
module Slot₀ = Model.Target 0 (ss s0)
actual-slot : U.U 0 Slot₀.default (W.φ Body.Model₀.p (ss s0)
  (L.add Body.Model₀.Z (P.σ Body.Model₀.p) (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1))))
actual-slot = Slot₀.result z≤n
```
