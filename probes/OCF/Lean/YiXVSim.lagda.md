# YiXV：第 1 层带底折叠的上界模拟
> 验收文件。编译定理 `Sim.upper`：关系域 `Sim.U` 中的树，其两种目标层 0 折叠都有参照上界。
> 只对有 `U` 推导的输入，不对一切合法层号。实际前缀底的实例见 `YiXVLocal`；全链上界仍未实填。
> 结点用 `YiXVNode`；第 0 层折叠与加法尾部用 `YiCeilRead`；参照正规片段复用 `YiOverRef`、`YiOverOps`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiCeilRead using (pw; ωx; pw-mono; next≼; fold₀≼; folds₀≼; ωx-mono)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ≼l)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVNode as N

pw-add : (σ′ : L.Simᴵ L.zero (L.suc L.zero)) (X : R.T₁) (y : T₀) → pw (L.ψ⁰ X) y ≼ L.ψ⁰ (L.add X σ′ y)
pw-add σ′ X L.zero = ≼-refl (L.ψ⁰ X)
pw-add σ′ X (L.suc y) = ωx-mono (pw-add σ′ X y)
pw-add σ′ X (L.lim f) = l≼ (λ n → ≼l n (pw-add σ′ X (f n)))
pw-add σ′ X (L.limᵢ () f)
pw-add σ′ X (L.up () y)

module AtNode (B : Base (suc zero)) (g : Tr zero → Tr (suc zero))
  (f : T₀ → R.T₁) (sc : O.SC f)
  (IH : (a : Tr zero) (y : T₀) → R.𝟙 ≼ y → L.suc (read a) ≼ y →
    (read (ψ⊥ (suc zero) tt tt B (g a)) ≼ L.ψ⁰ (f y)) ×
    (read (ψs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (g a)) ≼ L.ψ⁰ (f y))) where
  module Bot = N.Node f sc
    (λ a → ψ⊥ (suc zero) tt tt B (g a))
    (λ a → ψs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (g a))
    (λ a y o q → proj₁ (IH a y o q)) (λ a y o q → proj₂ (IH a y o q))
  module Slot = N.Node f sc
    (λ a → ψs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (g a))
    (λ a → ψs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (g a))
    (λ a y o q → proj₂ (IH a y o q)) (λ a y o q → proj₂ (IH a y o q))

  both : (read (ψ⊥ (suc zero) tt tt B (Ω (inj₁ tt) g)) ≼ L.ψ⁰ (L.limᵢ L.zero f)) ×
    (read (ψs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (Ω (inj₁ tt) g)) ≼ L.ψ⁰ (L.limᵢ L.zero f))
  both = Bot.result (λ n → nz⊥ (suc zero) tt tt B (g (Bot.c n))) ,
    Slot.result (λ n → nzs (suc zero) tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (g (Slot.c n)))

module Sim (B : Base (suc zero)) where
  β : Tr zero
  β = bs B zero (ins self)
  nβ : zero ⊢ zero ◃ β
  nβ = ns B zero (ins self)

  data U : Tr (suc zero) → R.T₁ → Set where
    uz : ∀ {X} → read (b⊥ B) ≼ L.ψ⁰ X → read β ≼ L.ψ⁰ X → U zero X
    us : ∀ {x X} → U x X → U (suc x) (L.suc X)
    uw : ∀ {x X Y} → O.Gd X → U x X → X R.≤ₚ Y → U x Y
    ul : ∀ {g a X} → (∀ n → U (g n) X) → U (lim g a) X
    un : ∀ {g f} → (∀ (a : Tr zero) (y : T₀) → L.suc (read a) ≼ y → U (g a) (f y)) →
      U (Ω (inj₁ tt) g) (L.limᵢ L.zero f)
    uu : ∀ {x y ny X Y} {σ′ : L.Simᴵ L.zero (L.suc L.zero)} → O.Gd X → U x X → read y ≼ Y → U (up x tt y ny) (L.add X σ′ Y)

  Both : Tr (suc zero) → R.T₁ → Set
  Both x X = (read (ψ⊥ (suc zero) tt tt B x) ≼ L.ψ⁰ X) ×
    (read (ψs (suc zero) tt tt B zero (ins self) β nβ x) ≼ L.ψ⁰ X)

  upper : ∀ {x X} → O.Gd X → U x X → Both x X
  upper gd (uz p q) = p , q
  upper (O.gs gd) (us {x = x} h) =
    next≼ (ψ⊥ (suc zero) tt tt B x) (nz⊥ (suc zero) tt tt B x) (proj₁ (upper gd h)) ,
    next≼ (ψs (suc zero) tt tt B zero (ins self) β nβ x) (nzs (suc zero) tt tt B zero (ins self) β nβ x) (proj₂ (upper gd h))
  upper gd (uw gdX h q) = ≼-trans (proj₁ (upper gdX h)) (R.mono⁰ q) , ≼-trans (proj₂ (upper gdX h)) (R.mono⁰ q)
  upper gd (ul h) = l≼ (λ n → proj₁ (upper gd (h n))) , l≼ (λ n → proj₂ (upper gd (h n)))
  upper (O.gi {f = f} law gb) (un {g = g} h) = AtNode.both B g f law (λ a y o q → upper (gb y o) (h a y q))
  upper gd (uu {x = x} {y = y} {X = X} {Y = Y} {σ′ = σ′} gdX h q) =
    ≼-trans (fold₀≼ (dS zero tt tt B x) (proj₁ (upper gdX h)) y)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ X)) q) (pw-add σ′ X Y)) ,
    ≼-trans (folds₀≼ (dS zero tt tt B x) (ψs (suc zero) tt tt B zero (ins self) β nβ x) (nzs (suc zero) tt tt B zero (ins self) β nβ x)
      (proj₂ (upper gdX h)) y)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ X)) q) (pw-add σ′ X Y))
```
