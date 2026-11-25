# 按表参数化: T2Desc

参数化（工程），数学内容与 `YiVTT2Desc` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMT2Desc where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (Σ; _,_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import OCF.Lean.YiLegBlock
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead using (read; ◃⊑; limcum≽)
  import OCF.Lean.YiMEBase as MB
  open import OCF.Lean.YiMEBase using (M⁰; mL; module Gen)
  import OCF.Lean.YiPMMEAnchor
  open OCF.Lean.YiPMMEAnchor.F tb using (ψ₀ᵗ; module G⁰)
  import OCF.Lean.YiPMMEStep
  open OCF.Lean.YiPMMEStep.F tb using (Step₂⁺ᴸ; h₂; c₂; row; nzrow; γ₊)
  import OCF.Align.EboLeanDef as E
  open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ⊑→≼)

  infix 4 _⊑¹_
  data _⊑¹_ (j : L) : L → Set where
    r¹ : j ⊑¹ j
    s¹ : ∀ {a} → j ⊑¹ a → j ⊑¹ suc a
    l¹ : ∀ {g} → j ⊑¹ g zero → j ⊑¹ lim g
    w¹ : ∀ {k h} → j ⊑¹ h zero → j ⊑¹ Ωₗ k h

  ev¹ : ∀ {j ℓ} → j ⊑¹ ℓ → Ev ℓ → Ev j
  ev¹ r¹     ε = ε
  ev¹ (s¹ p) ε = ev¹ p ε
  ev¹ (l¹ p) ε = ev¹ p (ε zero)
  ev¹ (w¹ p) ε = ev¹ p (proj₂ (proj₂ ε zero))

  rt¹ : ∀ {j ℓ} → j ⊑¹ ℓ → Rt ℓ → Rt j
  rt¹ r¹     ρ = ρ
  rt¹ (s¹ p) ρ = rt¹ p ρ
  rt¹ (l¹ p) ρ = rt¹ p (proj₁ ρ zero)
  rt¹ (w¹ p) ρ = rt¹ p (proj₂ ρ zero)

  lift¹ : (a b : L) → a ⊑¹ a ⊕ b
  lift¹ a zero     = r¹
  lift¹ a (suc b)  = s¹ (lift¹ a b)
  lift¹ a (lim g)  = l¹ (lift¹ a (g zero))
  lift¹ a (Ωₗ k h) = w¹ (lift¹ a (h zero))

  module _ (a : L) (ε : Ev a) (ρ : Rt a) where
    cS : ℕ → Tr a
    cS = iter (λ z → ψs (suc a) ε ρ (B₀ (suc a)) a (ins self) (Ωt a) (Ωt-nz a) (up zero tt (suc z) (z◃s z))) zero

    FS : ℕ → Tr zero
    FS n = ψ⊥ (suc a) ε ρ (B₀ (suc a)) (up zero tt (suc (cS n)) (z◃s (cS n)))

    nzS : ∀ n → zero ⊢ zero ◃ FS n
    nzS n = nz⊥ (suc a) ε ρ (B₀ (suc a)) (up zero tt (suc (cS n)) (z◃s (cS n)))

    S-form : ψ₀ (suc a) ε ρ (Ωt (suc a)) ≡ limc FS nzS
    S-form = refl

    cS-step : ∀ n → cS (suc n) ≡ next (ψs a ε ρ (B₀ a) a self (Ωt a) (Ωt-nz a) (cS n))
                                      (nzs a ε ρ (B₀ a) a self (Ωt a) (Ωt-nz a) (cS n))
    cS-step n = refl

    FS-step : ∀ n → FS n ≡ next (ψ₀ a ε ρ (cS n)) (nz⊥ a ε ρ (B₀ a) (cS n))
    FS-step n = refl

    suc-first : zero ⊢ ψ₀ a ε ρ (Ωt a) ◃ FS 1
    suc-first = ◃t (◃l zero) (◃l zero)

    suc-step : read (ψ₀ a ε ρ (Ωt a)) ≼ read (ψ₀ (suc a) ε ρ (Ωt (suc a)))
    suc-step = limcum≽ FS nzS 1 (⊑→≼ (read (ψ₀ a ε ρ (Ωt a))) (◃⊑ suc-first))

  lim-step : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g))
    → zero ⊢ ψ₀ (g zero) (ε zero) (proj₁ ρ zero) (Ωt (g zero)) ◃ ψ₀ (lim g) ε ρ (Ωt (lim g))
  lim-step g ε ρ = ◃l zero

  Ω-step : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h))
    → zero ⊢ ψ₀ (h zero) (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (Ωt (h zero)) ◃ ψ₀ (Ωₗ k h) ε ρ (Ωt (Ωₗ k h))
  Ω-step k h ε ρ = ◃l zero

  desc : ∀ {j ℓ} (p : j ⊑¹ ℓ) (ε : Ev ℓ) (ρ : Rt ℓ)
    → read (ψ₀ j (ev¹ p ε) (rt¹ p ρ) (Ωt j)) ≼ read (ψ₀ ℓ ε ρ (Ωt ℓ))
  desc {j} r¹ ε ρ = ≼-refl (read (ψ₀ j ε ρ (Ωt j)))
  desc (s¹ {a} p) ε ρ = ≼-trans (desc p ε ρ) (suc-step a ε ρ)
  desc (l¹ {g} p) ε ρ =
    ≼-trans (desc p (ε zero) (proj₁ ρ zero)) (⊑→≼ (read (ψ₀ (g zero) (ε zero) (proj₁ ρ zero) (Ωt (g zero)))) (◃⊑ (lim-step g ε ρ)))
  desc (w¹ {k} {h} p) ε ρ =
    ≼-trans (desc p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero))
      (⊑→≼ (read (ψ₀ (h zero) (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (Ωt (h zero)))) (◃⊑ (Ω-step k h ε ρ)))

  ε₁ : Ev (h₂ (c₂ 1))
  ε₁ = proj₂ (proj₂ (Ev-tw 2) (c₂ 1))

  ρ₁ : Rt (h₂ (c₂ 1))
  ρ₁ = proj₂ (Rt-tw 2) (c₂ 1)

  row1-form : row 1 ≡ ψ₀ (h₂ (c₂ 1)) ε₁ ρ₁ (Ωt (h₂ (c₂ 1)))
  row1-form = refl

  path⁺ : suc (tw 1) ⊑¹ h₂ (c₂ 1)
  path⁺ = w¹ (l¹ (w¹ r¹))

  ev-form : ev¹ path⁺ ε₁ ≡ Ev-tw 1
  ev-form = refl

  rt-form : rt¹ path⁺ ρ₁ ≡ Rt-tw 1
  rt-form = refl

  T⁺ : Tr zero
  T⁺ = ψ₀ (suc (tw 1)) (Ev-tw 1) (Rt-tw 1) (Ωt (suc (tw 1)))

  sucΩ≼tw2 : read T⁺ ≼ read (twᶜ 2)
  sucΩ≼tw2 = ≼-trans (desc path⁺ ε₁ ρ₁) (limcum≽ row nzrow 1 (≼-refl (read (row 1))))

  d⁺ : ℕ → Tr (tw 1)
  d⁺ = cS (tw 1) (Ev-tw 1) (Rt-tw 1)

  R⁺ : ℕ → Tr zero
  R⁺ = FS (tw 1) (Ev-tw 1) (Rt-tw 1)

  nzR⁺ : ∀ n → zero ⊢ zero ◃ R⁺ n
  nzR⁺ = nzS (tw 1) (Ev-tw 1) (Rt-tw 1)

  T⁺-form : T⁺ ≡ limc R⁺ nzR⁺
  T⁺-form = refl

  d⁺1 : d⁺ 1 ≡ next (Ωt (tw 1)) (Ωt-nz (tw 1))
  d⁺1 = refl

  rdLM : (x : Tr zero) → read x ≼ MB.read x
  rdLM zero          = z≼
  rdLM (suc x)       = s≼s (rdLM x)
  rdLM (lim f _)     = l≼ (λ n → ≼l n (rdLM (f n)))
  rdLM (Ω () _)
  rdLM (up _ () _ _)

  rdML : (x : Tr zero) → MB.read x ≼ read x
  rdML zero          = z≼
  rdML (suc x)       = s≼s (rdML x)
  rdML (lim f _)     = l≼ (λ n → ≼l n (rdML (f n)))
  rdML (Ω () _)
  rdML (up _ () _ _)

  step⁺-suc : (∀ n → Σ ℕ λ k → M⁰ (ψ₀ᵗ (γ₊ n)) (R⁺ k)) → Step₂⁺ᴸ
  step⁺-suc prem h =
    ≼-trans (MB.lower⁰ (mL {x = T⁺} refl (λ n → G⁰.m-cum R⁺ nzR⁺ (proj₁ (prem n)) (proj₂ (prem n)))) h)
      (≼-trans (rdML T⁺) (≼-trans sucΩ≼tw2 (rdLM (twᶜ 2))))
```
