# YiXVCountableGamma
> 验收文件。档位：编译定理。任意 Strong 层号上的原 Ψ 迭代链合法、后继有余量，并吸收一轮加法。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableGamma where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableAdd as Add
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableAddFrame as Plus
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFold as Fold
import OCF.Lean.YiXVCountableFoldOmega as FO
import OCF.Lean.YiXVCountableIter as I
module At (κ : L.Ordᴵ) (sκ : Strong κ) where
  module D = A.Layer κ A.Gd< A.Le<
  Ψ : L.Ordᶜ κ → L.Ordᶜ κ
  Ψ X = L.ψ L.zero (λ q → L.suc q) X
  Γ : ℕ → L.Ordᶜ κ
  Γ = iter Ψ (L.Ω κ)
  ψ-good : ∀ {X} → A.Gd X → A.Gd (Ψ X)
  ψ-good = Q.Ops.good (Fold.ops κ sκ) {ν = κ} {a = L.suc κ} sκ L.zero (λ q → L.suc q)
  ψ-mono : ∀ {X Y} → A.Le X Y → A.Le (Ψ X) (Ψ Y)
  ψ-mono = Q.Ops.mono (Fold.ops κ sκ) {ν = κ} {a = L.suc κ} {b = L.suc κ}
    sκ sκ L.zero L.zero (λ q → L.suc q) (λ q → L.suc q)
  good : ∀ n → A.Gd (Γ n)
  good zero = proj₁ (O.model κ)
  good (suc n) = ψ-good (good n)
  inv-Ω : A.Le (L.suc (L.Ω κ)) (Ψ (L.Ω κ))
  inv-Ω = D.trans (Plus.mixed {σ = λ q → q} {τ = λ q → q} (D.rfl (good zero)) (proj₂ (O.model κ)))
    (FO.two {κ = κ} {ν = κ} {a = L.suc κ} sκ sκ L.zero (λ q → L.suc q))
  inv : ∀ n → A.Le (L.suc (Γ n)) (Γ (suc n))
  inv zero = inv-Ω
  inv (suc n) = D.trans (I.strict {κ = κ} {ν = κ} {a = L.suc κ} L.zero (λ q → L.suc q) (Γ n) (good (suc n))) (ψ-mono (inv n))
  next : ∀ n → A.Le (Γ n) (Γ (suc n))
  next n = D.trans (D.pack (good n) (D.gs (good n)) (D.ws (D.rfl (good n)))) (inv n)
  step : ∀ {X} n → A.Le X (Γ n) → A.Le (X L.+ Ψ X) (Γ (suc (suc n)))
  step {X} n t = D.trans
    (D.pack (Add.good (D.left t) (ψ-good (D.left t))) (D.gl (I.good (Γ (suc n)) (good (suc n))))
      (D.lr 2 (Plus.mixed {σ = λ q → q} {τ = λ q → q} (D.trans t (next n)) (ψ-mono t))))
    (ψ-mono (inv n))
actual : A.Le (L.Ω L.ωᴵ L.+ At.Ψ L.ωᴵ Fold.ω-strong (L.Ω L.ωᴵ)) (At.Γ L.ωᴵ Fold.ω-strong 2)
actual = At.step L.ωᴵ Fold.ω-strong 0 (A.Layer.rfl L.ωᴵ A.Gd< A.Le< A.omegaΩ)
```
