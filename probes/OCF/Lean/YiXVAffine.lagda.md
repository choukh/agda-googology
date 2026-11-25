# YiXV：不同源底的带前缀上界保持
> 验收文件。条件定理：输入带 U/Closed/Good，源底两个目标层 0 分量界于 ψ₀X，则两种第 1 层目标 0 折叠界于 ψ₀(X+Y)。
> 不把结论扩为一切合法树；源底、比较底与参照前缀分别携带。实际含 pre 1 的孩子底在 YiXVWorld3 实填。
> 按 YiXVSim.upper 推广；节点用 YiXVNum/AffRef，幂与固定尾部结合由共用接口供给。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVAffine where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiCeilRead using (pw; ωx; pw-mono; next≼; fold₀≼; folds₀≼; ωx-mono)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ≼l)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVNum as N
import OCF.Lean.YiXVAffRef as AR

pw-add : ∀ {κ} (σ : L.Simᴵ L.zero κ) (X : L.Ordᶜ κ) (y : T₀) → pw (L.ψ⁰ X) y ≼ L.ψ⁰ (L.add X σ y)
pw-add σ X L.zero = ≼-refl _
pw-add σ X (L.suc y) = ωx-mono (pw-add σ X y)
pw-add σ X (L.lim f) = l≼ (λ n → ≼l n (pw-add σ X (f n)))
pw-add σ X (L.limᵢ () f)
pw-add σ X (L.up () y)

module AtNode (SrcB : Base (suc zero)) (X : F.T₂) (rx : X F.≤₂ X)
  (g : Tr zero → Tr (suc zero)) (f : T₀ → R.T₁) (sc : O.SC f)
  (IH : ∀ a y → R.𝟙 ≼ y → L.suc (read a) ≼ y →
    (read (ψ⊥ (suc zero) tt tt SrcB (g a)) ≼ L.ψ⁰ (L.add X A.σ₁ (f y))) ×
    (read (ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g a)) ≼ L.ψ⁰ (L.add X A.σ₁ (f y)))) where
  module V = AR.Aff X rx f sc
  module Bot = N.Node V.P V.ν V.norm
    (λ a → ψ⊥ (suc zero) tt tt SrcB (g a))
    (λ a → ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g a))
    (λ a y o q → proj₁ (IH a y o q)) (λ a y o q → proj₂ (IH a y o q))
  module Slot = N.Node V.P V.ν V.norm
    (λ a → ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g a))
    (λ a → ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g a))
    (λ a y o q → proj₂ (IH a y o q)) (λ a y o q → proj₂ (IH a y o q))
  both :
    (read (ψ⊥ (suc zero) tt tt SrcB (Ω (inj₁ tt) g)) ≼ L.ψ⁰ (L.add X A.σ₁ (L.limᵢ L.zero f))) ×
    (read (ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (Ω (inj₁ tt) g)) ≼ L.ψ⁰ (L.add X A.σ₁ (L.limᵢ L.zero f)))
  both = Bot.result (λ n → nz⊥ (suc zero) tt tt SrcB (g (Bot.c n))) ,
    Slot.result (λ n → nzs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g (Slot.c n)))

module Affine (Comp SrcB : Base (suc zero)) (X : F.T₂) (rx : X F.≤₂ X)
  (b : read (b⊥ SrcB) ≼ L.ψ⁰ X) (s : read (bs SrcB zero (ins self)) ≼ L.ψ⁰ X) where
  module U = S.Sim Comp
  module C = H.Anchor Comp
  β = bs SrcB zero (ins self)
  nβ = ns SrcB zero (ins self)
  Φ : R.T₁ → F.T₂
  Φ Y = L.add X A.σ₁ Y
  Both : Tr (suc zero) → R.T₁ → Set
  Both y Y = (read (ψ⊥ (suc zero) tt tt SrcB y) ≼ L.ψ⁰ (Φ Y)) ×
    (read (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y) ≼ L.ψ⁰ (Φ Y))
  upper : ∀ {y Y} → O.Gd Y → (h : U.U y Y) → C.Closed h → Both y Y
  upper gd (U.uz p q) refl = ≼-trans b (F.mono⁰ (A.right₂ rx (L.up L.zero O.Ω₁))) ,
    ≼-trans s (F.mono⁰ (A.right₂ rx (L.up L.zero O.Ω₁)))
  upper (O.gs gd) (U.us {x = y} h) c =
    next≼ (ψ⊥ (suc zero) tt tt SrcB y) (nz⊥ (suc zero) tt tt SrcB y) (proj₁ (upper gd h c)) ,
    next≼ (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y) (nzs (suc zero) tt tt SrcB zero (ins self) β nβ y) (proj₂ (upper gd h c))
  upper gd (U.uw gdY h q) c = ≼-trans (proj₁ (upper gdY h c)) (F.mono⁰ (A.tail rx q)) ,
    ≼-trans (proj₂ (upper gdY h c)) (F.mono⁰ (A.tail rx q))
  upper gd (U.ul h) c = l≼ (λ n → proj₁ (upper gd (h n) (c n))) , l≼ (λ n → proj₂ (upper gd (h n) (c n)))
  upper (O.gi {f = f} law gb) (U.un {g = g} h) c = AtNode.both SrcB X rx g f law
    (λ a y o q → upper (gb y o) (h a y q) (c a y q))
  upper gd (U.uu {x = y} {y = z} {X = Y} {Y = Z} {σ′ = σ} gdY h q) c =
    ≼-trans (fold₀≼ (dS zero tt tt SrcB y) (proj₁ (upper gdY h c)) z)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ (Φ Y))) q)
      (≼-trans (pw-add A.σ₀ (Φ Y) Z) (F.mono⁰ (A.assoc-tail X rx Y gdY σ Z)))) ,
    ≼-trans (folds₀≼ (dS zero tt tt SrcB y) (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y)
      (nzs (suc zero) tt tt SrcB zero (ins self) β nβ y) (proj₂ (upper gdY h c)) z)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ (Φ Y))) q)
      (≼-trans (pw-add A.σ₀ (Φ Y) Z) (F.mono⁰ (A.assoc-tail X rx Y gdY σ Z))))
```
