# ψ₀(Ω_Ω+Ω₃) 不高于 `TΛ`, 前提只剩第 2 层的对角定理

验收文件. 条件定理 `X₃≼ᵈ : Diag₂ᵀ → X₃ ≼ NA.read W.TΛ`; 前提 `Diag₂ᵀ` (静态对角线 ψ₂(Ω_{ℓ₀}) 在树的 Ω₁ 结点 `ψ₂ top` 之下, 关系 `⊴²`) 是第 1 层 [YiSyncDiag](YiSyncDiag.lagda.md) `Diag` 在第 2 层的对应. 链上逐点 `e₃⊴γ₃`, 前提 `Sync₃` 由 `fold2²` 给出 ([YiStepFold2](YiStepFold2.lagda.md)). 参照 `X₃` 读作 ψ₀(Ω_Ω+Ω₃), 读法是判断. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepThree where

open import Data.Nat.Base using (ℕ; zero; suc)
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextCore using (module G)
open import OCF.Align.YiLvVal2 using (ℓ₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiStepTree using (σ₃; σ₃′; ψ₂; γ₃; e₃; X₃; Sync₃; X₃≼ᶜ)
open import OCF.Lean.YiStepRel2 using (_⊴²_; Ω²⊴top; ⊴²-+ˡ)
open import OCF.Lean.YiStepFold2 using (cg₂; module F2)

Diag₂ᵀ : Set
Diag₂ᵀ = L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴² ψ₂ G.top

e₃-self : ∀ n → e₃ n L.≅ e₃ n
e₃-self zero = L.Ω-refl ℓ₂
e₃-self (suc n) = cg₂ σ₃′ (e₃-self n)

module C (D : Diag₂ᵀ) where
  open F2 D

  e₃⊴γ₃ : ∀ n → e₃ n ⊴² γ₃ n
  e₃⊴γ₃ zero = Ω²⊴top
  e₃⊴γ₃ (suc n) = ⊴²-+ˡ (γ₃ n) (Fold22 (e₃⊴γ₃ n) (e₃-self n))

  sync₃ : Sync₃
  sync₃ n = fold2² (e₃⊴γ₃ n) (e₃-self n)

X₃≼ᵈ : Diag₂ᵀ → X₃ ≼ NA.read W.TΛ
X₃≼ᵈ D = X₃≼ᶜ (C.sync₃ D)
```
