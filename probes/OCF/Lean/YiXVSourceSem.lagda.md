# YiXVSourceSem
> 验收文件。档位：编译定理。有限层世界语义：源模拟证书与基底界推出读回输出界；标准 Ω 实例逐层实填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceSem where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCanonicalInputs as C
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceWorldRules as Rules
import OCF.Lean.YiXVSourceWorldSelf as Self
import OCF.Lean.YiXVSourceWorldUp as Up
import OCF.Lean.YiXVSourceNodeBody as Body
import OCF.Lean.YiXVSourceWorldNode as Node

Sem : ℕ → Set
Sem n = ∀ {H} (p : P.Path H n) (SrcB : Fold.Base (J.nat n)) (Z : I.T H) →
  W.World n H p SrcB Z → ∀ {x X} → A.Gd n X → U.U n x X → W.Out n H p SrcB Z x X

module Stage (n : ℕ) (low : Sem n) where
  upper : Sem (suc n)
  upper p SrcB Z world gx U.Layer.uz = Rules.Rules.zero-out p SrcB Z world
  upper p SrcB Z world (A.Layer.gs gx) (U.Layer.us h) = Rules.Rules.suc-out p SrcB Z world gx (upper p SrcB Z world gx h)
  upper p SrcB Z world gy (U.Layer.uw h t@(A.Layer.pack gx _ _)) = Rules.Rules.weak-out p SrcB Z world
    (upper p SrcB Z world gx h) t
  upper p SrcB Z world gx (U.Layer.ul h) = Rules.Rules.lim-out p SrcB Z world (λ k → upper p SrcB Z world gx (h k))
  upper p SrcB Z world (A.Layer.gn law gb) (U.Layer.un i {g} {f} h) = Node.Node.result p SrcB Z world i g f law gb body
    where
    body : Body.Node.Body p SrcB Z world i g f
    Body.Node.Body.u body = h
    Body.Node.Body.out body a X Y gx gy o ha t = upper p SrcB Z world
      (gb (L.into (L.<→◃ (J.q n i)) Y) (C.At.good-in n (I.rank n i) (J.q n i) Y gy)
        (C.At.floor-in n (I.rank n i) (J.q n i) Y o)) (h a X Y gx gy o ha t)
  upper p SrcB Z world gout (U.Layer.uu {x} {y} {X} {Y} gx hx gy hy) = Up.Up.result p SrcB Z world gx hx gy hy prefix lower
    where
    prefix = upper p SrcB Z world gx hx
    lower = low (P.down p) (Fold.dS (J.nat n) (Default.ev (suc n)) (Default.rt (suc n)) SrcB x)
      (L.add Z (P.σ p) X) (Rules.child p SrcB Z world gx prefix) gy hy

upper : ∀ n → Sem n
upper zero p SrcB Z world gx h = Self.Base.result p SrcB Z world h
upper (suc n) = Stage.upper n (upper n)

actual : ∀ n H (p : P.Path H n) → W.Out n H p (Fold.B₀ (J.nat n)) (L.Ω (L.natᴵ H))
  (O.Ωt (J.nat n)) (L.Ω (L.natᴵ n) L.+ L.Ω (L.natᴵ n))
actual n H p = upper n p (Fold.B₀ (J.nat n)) (L.Ω (L.natᴵ H)) (W.model n H p)
  (Add.plus-good n {X = L.Ω (L.natᴵ n)} {Y = L.Ω (L.natᴵ n)} (proj₁ (B.Ω-model n F.zero)) (proj₁ (B.Ω-model n F.zero))) (UB.ΩU n)
```
