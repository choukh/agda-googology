# YiXVSourceWorldUp
> 验收文件。档位：编译定理。正有限源的 up 行世界输出界；实际前缀／孩子实例已填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldUp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (s0; ss)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceWorldRules as Rules
import OCF.Lean.YiXVSourceWorldSelf as Self

module Up {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) where
  module D = U.Layer n (U.UR n)
  Bchild : J.Tr (suc n) → Fold.Base (J.nat n)
  Bchild x = Fold.dS (J.nat n) (Model.ev (suc n)) (Model.rt (suc n)) SrcB x
  result : ∀ {x : J.Tr (suc n)} {X : I.T (suc n)} {y : J.Tr n} {Y : I.T n} {ny : J.nat n S.⊢ S.zero ◃ y} → A.Gd (suc n) X → D.U x X → A.Gd n Y → U.U n y Y →
    W.Out (suc n) H p SrcB Z x X →
    W.Out n H (P.down p) (Bchild x) (L.add Z (P.σ p) X) y Y →
    W.Out (suc n) H p SrcB Z (S.up x tt y ny) (L.add X (λ q → L.suc q) Y)
  W.Out.bot (result {X = X} {Y = Y} gx hx gy hy prefix lower) = ≼-trans (W.Out.bot {n = n} lower)
    (ZR.mono H (Compose.compose H (suc n) n Z (P.σ p) X (λ q → L.suc q) Y (W.World.good world) gx gy))
  W.Out.slots (result {X = X} {Y = Y} gx hx gy hy prefix lower) .(suc n) s0 = Self.Same.result p SrcB Z world
    (Add.good (suc n) n {X = X} gx (λ q → L.suc q) Y gy) (D.uu gx hx gy hy)
  W.Out.slots (result {X = X} {Y = Y} gx hx gy hy prefix lower) j (ss s) = UB.weakU j (W.Out.slots {n = n} lower j s)
    (W.φ-mix (P.down p) s p (ss s)
      (Compose.compose H (suc n) n Z (P.σ p) X (λ q → L.suc q) Y (W.World.good world) gx gy))

module Actual {n H} (p : P.Path H (suc n)) where
  SrcB : Fold.Base (J.nat (suc n))
  SrcB = Fold.B₀ (J.nat (suc n))
  Z : I.T H
  Z = L.Ω (L.natᴵ H)
  world : W.World (suc n) H p SrcB Z
  world = W.model (suc n) H p
  X : I.T (suc n)
  X = L.suc (L.Ω (L.natᴵ (suc n)))
  Y : I.T n
  Y = L.suc (L.Ω (L.natᴵ n))
  gx : A.Gd (suc n) X
  gx = B.gs (suc n) F.zero {X = L.Ω (L.natᴵ (suc n))} (proj₁ (B.Ω-model (suc n) F.zero))
  gy : A.Gd n Y
  gy = B.gs n F.zero {X = L.Ω (L.natᴵ n)} (proj₁ (B.Ω-model n F.zero))
  hx : U.U (suc n) (S.suc S.zero) X
  hx = UB.sucU (suc n) (UB.zeroU (suc n))
  hy : U.U n (S.suc S.zero) Y
  hy = UB.sucU n (UB.zeroU n)
  module R = Rules.Rules p SrcB Z world
  prefix : W.Out (suc n) H p SrcB Z (S.suc S.zero) X
  prefix = R.suc-out (proj₁ (B.Ω-model (suc n) F.zero)) R.zero-out
  Bchild : Fold.Base (J.nat n)
  Bchild = Fold.dS (J.nat n) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (S.suc S.zero)
  lowerWorld : W.World n H (P.down p) Bchild (L.add Z (P.σ p) X)
  lowerWorld = Rules.Actual.actual p
  module Child = Rules.Rules (P.down p) Bchild (L.add Z (P.σ p) X) lowerWorld
  lower : W.Out n H (P.down p) Bchild (L.add Z (P.σ p) X) (S.suc S.zero) Y
  lower = Child.suc-out (proj₁ (B.Ω-model n F.zero)) Child.zero-out
  actual : W.Out (suc n) H p SrcB Z (S.up (S.suc S.zero) tt (S.suc S.zero) S.◃s) (L.add X (λ q → L.suc q) Y)
  actual = Up.result p SrcB Z world gx hx gy hy prefix lower
```
