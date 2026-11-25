# YiXV：上界模拟对加法与 next 封闭
> 验收文件。编译定理：`Closure.plus-comp`、`next-comp` 保持 `YiXVSim.Sim.U`。
> 来源：源运算按定义展开，参照加法与正规片段复用 `YiOverOps`；第 0 层尾部只证明所需的结合方向。
> 用于实际回灌底的上折；不提供一般层号或整塔上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVPlus where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold using (Base)
open import OCF.Lean.YiLSRead using (T₀)
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

assoc-tail : ∀ {X Y : R.T₁} {σ τ : L.Simᴵ L.zero (L.suc L.zero)} → O.Gd X → O.Gd Y → (z : T₀) →
  L.add (X L.+ Y) σ z R.≤ₚ (X L.+ L.add Y τ z)
assoc-tail gX gY L.zero = O.reflₚ (O.Gd-+ gX gY)
assoc-tail gX gY (L.suc z) = R.ss (assoc-tail gX gY z)
assoc-tail gX gY (L.lim f) = R.l≤ (λ n → R.≤l n (assoc-tail gX gY (f n)))
assoc-tail gX gY (L.limᵢ () f)
assoc-tail gX gY (L.up () x)

module Closure (B : Base (suc zero)) where
  module A = S.Sim B
  open A using (U; uz; us; uw; ul; un; uu)

  plus-comp : ∀ {x X} → O.Gd X → U x X → ∀ {y Y} → O.Gd Y → U y Y → U (x + y) (X L.+ Y)
  plus-comp gX hx gY (uz {X = Y} p q) = uw gX hx (O.+ₚ (O.reflₚ gX) (O.z≤ Y))
  plus-comp gX hx (O.gs gY) (us hy) = us (plus-comp gX hx gY hy)
  plus-comp gX hx gY (uw gY₀ hy q) = uw (O.Gd-+ gX gY₀) (plus-comp gX hx gY₀ hy) (O.+ₚ (O.reflₚ gX) q)
  plus-comp gX hx gY (ul h) = ul (λ n → plus-comp gX hx gY (h n))
  plus-comp gX hx (O.gi law gb) (un h) = un (λ a y q → plus-comp gX hx (gb y (O.s→1 q)) (h a y q))
  plus-comp gX hx gY (uu {y = z} {X = Y₀} {Y = Z} {σ′ = σ′} gY₀ hy q) =
    uw (O.Gd-add⁰ (O.Gd-+ gX gY₀) Z)
      (uu {σ′ = σ′} (O.Gd-+ gX gY₀) (plus-comp gX hx gY₀ hy) q)
      (assoc-tail {σ = σ′} {τ = σ′} gX gY₀ Z)

  module Power {x X} (gX : O.Gd X) (hx : U x X) where
    terms : (n : ℕ) → U (iter (x +_) x n) (iterᴸ (X L.+_) L.zero (suc n))
    terms zero = hx
    terms (suc n) = plus-comp gX hx (O.Gd-iter gX (suc n)) (terms n)

  next-comp : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) → O.Gd X → U x X →
    U (next x nx) (L.lim (iterᴸ (X L.+_) L.zero))
  next-comp nx gX hx = ul (λ n → uw (O.Gd-iter gX (suc n)) (Power.terms gX hx n)
    (R.≤l (suc n) (O.reflₚ (O.Gd-iter gX (suc n)))))
```
