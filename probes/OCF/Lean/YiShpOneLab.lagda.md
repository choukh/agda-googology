# 参照 `X₁₂` 带 ψ₀(Ω_Ω+Ω₁·2) 的遗传标签

验收文件, 标签只在这里出现. 编译定理 `X₁₂-label : Lab X₁₂ x12ᵗ`, `x12ᵗ` 是 EBO 的 ψ₀(Ω_Ω+Ω₁+Ω₁). 办法照 [Stage2](../Align/Stage2.lagda.md) §8 的 `Ctx₀`: 前缀换成 `χ₁` 的树, 底由 `χ1-label` 给出.
被验收的值定理在 [YiShpOne](YiShpOne.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiShpOneLab where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Align.Level
import OCF.Align.EBO as E
open E using (T; cω; cof; cofA; fsn; fsT; γT; natT; dec) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
import OCF.Align.Stage2 as S2
open S2 using (Ωᵗ; Lab-rep; χ1-label; lab-χ0)
open import OCF.Lean.YiShpOne using (σA; fA; X₁₂; eA; fA-≅)
```

```agda
fA-cong : ∀ {Y Y′ : Ordᶜ zero} → Y ≅ Y′ → fA Y ≅ fA Y′
fA-cong e = add-≅ {σ = σA} {σ′ = σA} (Ω-refl S2.ℓ₀)
  (add-≅ {σ = λ q → suc q} {σ′ = λ q → suc q} (Ω-refl (suc zero)) e)

ctx₁ : T → T
ctx₁ y = ψᵗ [] (ψᵗ Ωᵗ [] ∷ ψᵗ (natT 1) [] ∷ y) ∷ []

Ctx₁ : ∀ {Y y} → Lab Y y → Lab (ψ⁰ (fA Y)) (ctx₁ y)
Ctx₁ {y = []}     (l0 c e) = Lab-≅ (ψ⁰-≅ (fA-cong e)) χ1-label
Ctx₁ {y = y ∷ ys} (l0 c e) = ⊥-elim (cof-ne y ys c)
Ctx₁ {y = []}     (l1 () e l)
Ctx₁ {y = y ∷ ys} (l1 c e l) =
  lω (cong (cofA []) c) (ψ⁰-≅ (fA-cong e))
     (λ n → subst (Lab _) (sym (fs-rep [] (ψᵗ Ωᵗ []) (ψᵗ (natT 1) [] ∷ y ∷ ys) c n)) (Lab-rep (Ctx₁ l) n))
Ctx₁ {y = []}     (lω () e h)
Ctx₁ {y = y ∷ ys} (lω c e h) =
  lω (cong (cofA []) c) (ψ⁰-≅ (fA-cong e))
     (λ n → subst (Lab _) (sym (fs-ω [] (ψᵗ Ωᵗ []) (ψᵗ (natT 1) [] ∷ y ∷ ys) c n)) (Ctx₁ (h n)))

b″ : T
b″ = ψᵗ Ωᵗ [] ∷ ψᵗ (natT 1) [] ∷ ψᵗ (natT 1) [] ∷ []

x12ᵗ : T
x12ᵗ = ψᵗ [] b″ ∷ []

_ : ∀ m → γT b″ [] (suc m) ≡ ctx₁ (γT b″ [] m)
_ = λ m → refl

fs-x12 : ∀ m → fsn x12ᵗ m ≡ ctx₁ (γT b″ [] m)
fs-x12 m = cong (λ z → ψᵗ [] z ∷ [])
  (trans (E.fsT↓-trm b″ refl (dec (E.γ↓ b″ [] refl m))) (cong (fsT b″) (E.γ↓-trm b″ [] refl m)))

lab-eA : ∀ m → Lab (eA m) (γT b″ [] m)
lab-eA zero    = lab-χ0
lab-eA (suc m) = Lab-≅ (≅-sym (ψ⁰≅ψ {p = lim 0 zero} {σ = λ r → r} (fA-≅ (eA m)))) (Ctx₁ (lab-eA m))

X₁₂-label : Lab X₁₂ x12ᵗ
X₁₂-label = lω refl (l≅ (λ m → ≅-refl⁰ _)) (λ m → subst (Lab _) (sym (fs-x12 m)) (Ctx₁ (lab-eA m)))
```
