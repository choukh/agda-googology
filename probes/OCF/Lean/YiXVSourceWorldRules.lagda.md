# YiXVSourceWorldRules
> 验收文件。档位：编译定理。零、后继、弱化、极限行与孩子基底保持。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldRules where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiCeilRead using (next≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans; l≼)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceNext as Next
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVSourceWorldInput as W

module Rules {n H} (p : P.Path H n) (SrcB : Fold.Base (J.nat n)) (Z : I.T H) (world : W.World n H p SrcB Z) where
  Result = W.Out n H p SrcB Z
  cap : I.T n → I.T H
  cap X = L.add Z (P.σ p) X
  cap-good : ∀ X → A.Gd n X → A.Gd H (cap X)
  cap-good X gx = Add.good H n {X = Z} (W.World.good world) (P.σ p) X gx
  zero-out : Result S.zero (L.Ω (L.natᴵ n))
  W.Out.bot zero-out = ≼-trans (W.World.bot world) (ZR.mono H raise)
    where
    raise = Right.right H n (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p)
      (L.Ω (L.natᴵ n)) (proj₁ (B.Ω-model n F.zero))
  W.Out.slots zero-out j s = UB.weakU j (W.World.slots world j s) (W.φ-mix p s p s raise)
    where
    raise = Right.right H n (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p)
      (L.Ω (L.natᴵ n)) (proj₁ (B.Ω-model n F.zero))

  suc-out : ∀ {x X} → A.Gd n X → Result x X → Result (S.suc x) (L.suc X)
  W.Out.bot (suc-out {x} gx h) = next≼ _ (Fold.nz⊥ (J.nat n) (Model.ev n) (Model.rt n) SrcB x) (W.Out.bot h)
  W.Out.slots (suc-out {x} {X} gx h) j s = Next.next j
    (Fold.nzs (J.nat n) (Model.ev n) (Model.rt n) SrcB (J.nat j) (Slots.pth s)
      (Fold.bs SrcB (J.nat j) (Slots.pth s)) (Fold.ns SrcB (J.nat j) (Slots.pth s)) x)
    (W.φ-good p s (cap-good X gx)) (W.Out.slots h j s)

  weak-out : ∀ {x X Y} → Result x X → A.Le n X Y → Result x Y
  W.Out.bot (weak-out {X = X} {Y} h t) = ≼-trans (W.Out.bot h) (ZR.mono H
    (Add.mono H n {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) X Y t))
  W.Out.slots (weak-out {X = X} {Y} h t) j s = UB.weakU j (W.Out.slots h j s)
    (W.φ-mix p s p s (Add.mono H n {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} (W.World.good world)) (P.σ p) X Y t))

  lim-out : ∀ {g a X} → (∀ k → Result (g k) X) → Result (S.lim g a) X
  W.Out.bot (lim-out h) = l≼ (λ k → W.Out.bot (h k))
  W.Out.slots (lim-out h) j s = UB.limU j (λ k → W.Out.slots (h k) j s)

child : ∀ {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H) →
  W.World (suc n) H p SrcB Z → ∀ {x X} → A.Gd (suc n) X → W.Out (suc n) H p SrcB Z x X →
  W.World n H (P.down p) (Fold.dS (J.nat n) (Model.ev (suc n)) (Model.rt (suc n)) SrcB x) (L.add Z (P.σ p) X)
W.World.good (child {n} {H} p SrcB Z world {X = X} gx h) = Add.good H (suc n) {X = Z} (W.World.good world) (P.σ p) X gx
W.World.bot (child p SrcB Z world gx h) = W.Out.bot h
W.World.slots (child {n} {H} p SrcB Z world {X = X} gx h) j s = UB.weakU j (W.Out.slots h j (ss s))
  (W.φ-mix p (ss s) (P.down p) s (B.rfl H F.zero {X = L.add Z (P.σ p) X}
    (Add.good H (suc n) {X = Z} (W.World.good world) (P.σ p) X gx)))

module Actual {n H} (p : P.Path H (suc n)) where
  SrcB = Fold.B₀ (J.nat (suc n))
  Z = L.Ω (L.natᴵ H)
  world = W.model (suc n) H p
  module R = Rules p SrcB Z world
  actual : W.World n H (P.down p)
    (Fold.dS (J.nat n) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (S.suc S.zero))
    (L.add Z (P.σ p) (L.suc (L.Ω (L.natᴵ (suc n)))))
  actual = child p SrcB Z world (B.gs (suc n) F.zero {X = L.Ω (L.natᴵ (suc n))} (proj₁ (B.Ω-model (suc n) F.zero)))
    (R.suc-out (proj₁ (B.Ω-model (suc n) F.zero)) R.zero-out)
```
