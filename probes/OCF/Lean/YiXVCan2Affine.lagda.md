# YiXV: 更新孩子底的读回保持
> 验收文件。档位：编译定理。由 YiXVAffine 改写；输入带 U/Closed/Good，两个目标 0 输出都有 ψ₀(X+Y) 上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Affine where
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
import OCF.Lean.YiXVCan2AffRef as AR
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Add as CA
import OCF.Lean.YiXVCan2Zero as Z
open import OCF.Lean.YiXVAffine using (pw-add)

module AtNode (SrcB : Base (suc zero)) (X : F.T₂) (gx : C.Gd X)
  (g : Tr zero → Tr (suc zero)) (f : T₀ → R.T₁) (sc : O.SC f) (gb : ∀ y → R.𝟙 ≼ y → O.Gd (f y))
  (IH : ∀ a y → R.𝟙 ≼ y → L.suc (read a) ≼ y →
    (read (ψ⊥ (suc zero) tt tt SrcB (g a)) ≼ L.ψ⁰ (L.add X A.σ₁ (f y))) ×
    (read (ψs (suc zero) tt tt SrcB zero (ins self) (bs SrcB zero (ins self)) (ns SrcB zero (ins self)) (g a)) ≼ L.ψ⁰ (L.add X A.σ₁ (f y)))) where
  module V = AR.Aff X gx f sc gb
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

module Affine (Comp SrcB : Base (suc zero)) (X : F.T₂) (gx : C.Gd X)
  (b : read (b⊥ SrcB) ≼ L.ψ⁰ X) (s : read (bs SrcB zero (ins self)) ≼ L.ψ⁰ X) where
  module U = S.Sim Comp
  module HC = H.Anchor Comp
  β = bs SrcB zero (ins self)
  nβ = ns SrcB zero (ins self)
  Φ : R.T₁ → F.T₂
  Φ Y = L.add X A.σ₁ Y
  Both : Tr (suc zero) → R.T₁ → Set
  Both y Y = (read (ψ⊥ (suc zero) tt tt SrcB y) ≼ L.ψ⁰ (Φ Y)) ×
    (read (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y) ≼ L.ψ⁰ (Φ Y))
  upper : ∀ {y Y} → O.Gd Y → (h : U.U y Y) → HC.Closed h → Both y Y
  upper gd (U.uz p q) refl = ≼-trans b (Z.mono₀ (CA.rightE (C.refl gx) (C.gu O.Gd-Ω) (M.good₁ gx O.Gd-Ω))) ,
    ≼-trans s (Z.mono₀ (CA.rightE (C.refl gx) (C.gu O.Gd-Ω) (M.good₁ gx O.Gd-Ω)))
  upper (O.gs gd) (U.us {x = y} h) c =
    next≼ (ψ⊥ (suc zero) tt tt SrcB y) (nz⊥ (suc zero) tt tt SrcB y) (proj₁ (upper gd h c)) ,
    next≼ (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y) (nzs (suc zero) tt tt SrcB zero (ins self) β nβ y) (proj₂ (upper gd h c))
  upper gd (U.uw gdY h q) c = ≼-trans (proj₁ (upper gdY h c)) (Z.mono₀ (M.tail (C.refl gx) gdY gd q)) ,
    ≼-trans (proj₂ (upper gdY h c)) (Z.mono₀ (M.tail (C.refl gx) gdY gd q))
  upper gd (U.ul h) c = l≼ (λ n → proj₁ (upper gd (h n) (c n))) , l≼ (λ n → proj₂ (upper gd (h n) (c n)))
  upper (O.gi {f = f} law gb) (U.un {g = g} h) c = AtNode.both SrcB X gx g f law gb
    (λ a y o q → upper (gb y o) (h a y q) (c a y q))
  upper gd (U.uu {x = y} {y = z} {X = Y} {Y = Z} {σ′ = σ} gdY h q) c =
    ≼-trans (fold₀≼ (dS zero tt tt SrcB y) (proj₁ (upper gdY h c)) z)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ (Φ Y))) q)
      (≼-trans (pw-add A.σ₀ (Φ Y) Z) (Z.mono₀ (AR.assoc gx gdY σ Z)))) ,
    ≼-trans (folds₀≼ (dS zero tt tt SrcB y) (ψs (suc zero) tt tt SrcB zero (ins self) β nβ y)
      (nzs (suc zero) tt tt SrcB zero (ins self) β nβ y) (proj₂ (upper gdY h c)) z)
      (≼-trans (pw-mono (≼-refl (L.ψ⁰ (Φ Y))) q)
      (≼-trans (pw-add A.σ₀ (Φ Y) Z) (Z.mono₀ (AR.assoc gx gdY σ Z))))
```
