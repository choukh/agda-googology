# 上折: 折叠

> 判决: 成品候选 (折叠). 与 `YiPhiFold` 不同的是自身行一处: 目标是 ℓ 自身时, `up x c y` 的输出是孩子 y 的上折 (`YiUpBlock.Upc`), 底是 x 对自身的折叠; 原来是把 y 原样留下.
> 保留判定 `kp` 取自 `YiPhiFold`, 不改. 其余各行逐字相同 (两个折叠互递归, 所以整段重写).
> 不否定什么. 合法性在 `YiUpLegal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ; eqℕ-refl)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiUpBlock
```

## 折叠

```agda
mutual
  ψ⊥ : (ℓ : L) → Ev ℓ → Base ℓ → Tr ℓ → Tr zero
  ψ⊥ ℓ ε B zero    = b⊥ B
  ψ⊥ ℓ ε B (suc x) = next (ψ⊥ ℓ ε B x)
  ψ⊥ ℓ ε B (lim f) = lim (λ n → ψ⊥ ℓ ε B (f n))
  ψ⊥ ℓ ε B (Ω p g) = lim (cum (λ n → ψ⊥ ℓ ε B (g (iter step (fromBr ℓ p zero) n))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψ⊥ (suc a)  ε B (up x _ y) =
    ψ⊥ a ε (base (ψ⊥ (suc a) ε B x) (λ j w → ψs (suc a) ε B j (ins w) (bs B j (ins w)) x)) y
  ψ⊥ (lim g)  ε B (up x n y) =
    ψ⊥ (g n) (ε n) (base (ψ⊥ (lim g) ε B x) (λ j w → ψs (lim g) ε B j (inl n w) (bs B j (inl n w)) x)) y
  ψ⊥ (Ωₗ k h) ε B (up x c y) =
    ψ⊥ (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x)) y
  ψ⊥ zero     ε B (up x () y)

  ψs : (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j
  ψs ℓ ε B j w β zero    = β
  ψs ℓ ε B j w β (suc x) = next (ψs ℓ ε B j w β x)
  ψs ℓ ε B j w β (lim f) = lim (λ n → ψs ℓ ε B j w β (f n))
  ψs ℓ ε B j w β (Ω p g) =
    kp ℓ ε p w (λ q cv → Ω q (λ z → ψs ℓ ε B j w β (g (cv z))))
               (lim (cum (λ n → ψs ℓ ε B j w β (g (iter step (fromBr ℓ p zero) n)))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψs ℓ ε B _ self β (up x c y) = Upc ℓ c (ψs ℓ ε B ℓ self β x) y
  ψs (suc a) ε B j (ins w) β (up x _ y) =
    ψs a ε (base (ψ⊥ (suc a) ε B x) (λ j′ w′ → ψs (suc a) ε B j′ (ins w′) (bs B j′ (ins w′)) x))
      j w (ψs (suc a) ε B j (ins w) β x) y
  ψs (lim g) ε B j (inl n w) β (up x m y) with eqℕ m n
  ... | just refl =
    ψs (g m) (ε m) (base (ψ⊥ (lim g) ε B x) (λ j′ w′ → ψs (lim g) ε B j′ (inl m w′) (bs B j′ (inl m w′)) x))
      j w (ψs (lim g) ε B j (inl m w) β x) y
  ... | nothing   = ψs (lim g) ε B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (B₀ (g m)) y)
  ψs (lim g) ε B j (inlu ws) β (up x m y) =
    ψs (g m) (ε m) (base (ψ⊥ (lim g) ε B x) (λ j′ w′ → ψs (lim g) ε B j′ (inl m w′) (bs B j′ (inl m w′)) x))
      j (ws m) (ψs (lim g) ε B j (inlu ws) β x) y
  ψs (Ωₗ k h) ε B j (ink w) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j′ w′ → ψs (Ωₗ k h) ε B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε B j (ink w) β x) y
  ψs (Ωₗ k h) ε B j (inu ws) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j′ w′ → ψs (Ωₗ k h) ε B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (ws c) (ψs (Ωₗ k h) ε B j (inu ws) β x) y
  ψs (Ωₗ k h) ε B j (inb c′ w) β (up x c y) =
    ψs (Ωₗ k h) ε B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) y)

ψ₀ : (ℓ : L) → Ev ℓ → Tr ℓ → Tr zero
ψ₀ ℓ ε = ψ⊥ ℓ ε (B₀ ℓ)
```
