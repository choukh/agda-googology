# 按表参数化: T2Frame

参数化（工程），数学内容与 `YiVTT2Frame` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMT2Frame where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)
  open import Data.Maybe using (just; nothing)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import OCF.Lean.YiLegBlock renaming (L to LF)
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead
  open import OCF.Lean.YiLSRel using (Corr)
  import OCF.Lean.YiPMLSFold
  open OCF.Lean.YiPMLSFold.F tb using (NL; OKB; ok-B₀; lower; ψ⊥-⊵; ψs-⊵)
  import OCF.Lean.YiPMLSTw1
  open OCF.Lean.YiPMLSTw1.F tb using (h₁; εh; ρh; G; nl-↑; corr-↑; lvl; E; ez; es; el; E-next; E-cum; E→≅; LiftP; LiftP-∙; eq0)
  import OCF.Lean.YiPMT2Desc
  open OCF.Lean.YiPMT2Desc.F tb using (R⁺; nzR⁺; sucΩ≼tw2)

  import OCF.Align.Level as L
  open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
  import OCF.Align.EboLeanDef as E
  import OCF.Lean.YiPMMEAnchor
  open OCF.Lean.YiPMMEAnchor.F tb using (u₁; Ω₁ᵗ)
  open import Data.List using ([]; _∷_)

  ok-dW : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → OKB (Ωₗ k h) B
    → (c : Tr k) (t : Tr (Ωₗ k h)) → OKB (h c) (dW k h ε ρ B c t)
  ok-dW k h ε ρ B ok c t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (Ωₗ k h) ε ρ B t)
    , λ j w → ⊴-trans (proj₂ ok j (inb c w)) (ψs-⊵ (Ωₗ k h) ε ρ B j (inb c w) _ _ t)

  up-lower : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → OKB (Ωₗ k h) B
    → (x : Tr (Ωₗ k h)) (c : Tr k) → NL (h c) → ∀ {i} → Corr i (h c)
    → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ (Ωₗ k h) ε ρ B (up x c (Ωt (h c)) (Ωt-nz (h c))))
  up-lower k h ε ρ B ok x c f cr =
    lower f (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (ok-dW k h ε ρ B ok c x) cr

  fallback : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : LF)
    (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
    (e : h c ⊢ zero ◃ y)
    → tb k h c c′ ≡ nothing   -- 改: 原行只在表里没有条目时出现
    → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
    ≡ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ₀ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y)
  fallback k h ε ρ B j c′ w β nβ x c y e eq with tb k h c c′
  fallback k h ε ρ B j c′ w β nβ x c y e () | just (inj₁ _)
  fallback k h ε ρ B j c′ w β nβ x c y e () | just (inj₂ _)
  fallback k h ε ρ B j c′ w β nβ x c y e eq | nothing = refl

  inner-base : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
    (c : Tr k) (x : Tr (Ωₗ k h)) (j : LF) (w : j ≤ h c)
    → bs (dW k h ε ρ B c x) j w ≡ ψs (Ωₗ k h) ε ρ B j (inb c w) (bs B j (inb c w)) (ns B j (inb c w)) x
  inner-base k h ε ρ B c x j w = refl

  eqk : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (w : zero ≤ k)
    → ((c : Tr k) → LiftP (w ∙ proj₁ (proj₂ ε c)))
    → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → E β (b⊥ B)
    → (x : Tr (Ωₗ k h)) → E (ψs (Ωₗ k h) ε ρ B zero (ink w) β nβ x) (ψ⊥ (Ωₗ k h) ε ρ B x)
  eqk k h ε ρ B w lw β nβ e zero      = e
  eqk k h ε ρ B w lw β nβ e (suc x)   = E-next (eqk k h ε ρ B w lw β nβ e x)
  eqk k h ε ρ B w lw β nβ e (lim f a) = el (λ n → eqk k h ε ρ B w lw β nβ e (f n))
  eqk k h ε ρ B w lw β nβ e (Ω p g) =
    kp-ind (Ωₗ k h) ε ρ p (ink w) (λ X → E X (ψ⊥ (Ωₗ k h) ε ρ B (Ω p g))) (λ ())
      (E-cum _ _ (λ n → eqk k h ε ρ B w lw β nβ e (g _)))
  eqk k h ε ρ B w lw β nβ e (up x c y e′) =
    eq0 (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (w ∙ proj₁ (proj₂ ε c)) (lw c) _ _
      (eqk k h ε ρ B w lw β nβ e x) y

  ε¹ : Ev (tw 1)
  ε¹ = Ev-tw 1

  ρ¹ : Rt (tw 1)
  ρ¹ = Rt-tw 1

  β : Tr (tw 1)
  β = Ωt (tw 1)

  gβ : Tr zero → Tr (tw 1)
  gβ z = up β z (Ωt (h₁ z)) (Ωt-nz (h₁ z))

  zc : ℕ → Tr zero
  zc = iter (λ z → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (ink self) (Ωt zero) (Ωt-nz zero) (gβ z)) zero

  rowβ : ℕ → Tr zero
  rowβ n = ψ⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gβ (zc n))

  nzβ : ∀ n → zero ⊢ zero ◃ rowβ n
  nzβ n = nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gβ (zc n))

  ββ-form : ψ₀ (tw 1) ε¹ ρ¹ (β + β) ≡ limc rowβ nzβ
  ββ-form = refl

  row-lower : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (rowβ n)
  row-lower n = up-lower zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (ok-B₀ (tw 1)) β (zc n) (nl-↑ (zc n)) (corr-↑ (zc n) (HSr (zc n)))

  lw¹ : (c : Tr zero) → LiftP (self ∙ proj₁ (proj₂ ε¹ c))
  lw¹ c = LiftP-∙ zero (↑ zero c) self tt

  zc-row : ∀ n → E (zc (suc n)) (rowβ n)
  zc-row n = eqk zero h₁ ε¹ ρ¹ (B₀ (tw 1)) self lw¹ (Ωt zero) (Ωt-nz zero) (es ez) (gβ (zc n))

  row0-form : rowβ 0 ≡ next (twᶜ 1) (nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) β)
  row0-form = refl

  tw1◃row0 : zero ⊢ twᶜ 1 ◃ rowβ 0
  tw1◃row0 = ◃l zero

  chain-closed : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (zc (suc n))
  chain-closed n = ≼-trans (row-lower n) (≅→≼ (L.≅-sym (E→≅ (zc-row n))))

  ββ◃R1 : zero ⊢ ψ₀ (tw 1) ε¹ ρ¹ (β + β) ◃ R⁺ 1
  ββ◃R1 = ◃t (◃l 1) (◃l zero)

  ββ≼tw2 : read (ψ₀ (tw 1) ε¹ ρ¹ (β + β)) ≼ read (twᶜ 2)
  ββ≼tw2 = ≼-trans (limcum≽ R⁺ nzR⁺ 1 (⊑→≼ (read (ψ₀ (tw 1) ε¹ ρ¹ (β + β))) (◃⊑ ββ◃R1))) sucΩ≼tw2

  named : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (twᶜ 2)
  named n = ≼-trans (limcum≽ rowβ nzβ n (row-lower n)) ββ≼tw2

  one two : Tr zero
  one = suc zero
  two = suc one

  -- 改: 删去 β₁-form (原行在孩子 two 的底上的形状; 带表时分支 c 上先查表, 不再是这个形状)

  self-slot : (b : Tr (tw 1)) (nb : tw 1 ⊢ zero ◃ b)
    → Upc (tw 1) one b nb (Ωt (h₁ one))
    ≡ Ω (inj₂ (one , inj₂ (inj₁ tt))) (λ z → Up (suc zero) (down stop one) b nb (up zero tt (suc z) (z◃s z)))
  self-slot b nb = refl

  IsLim IsΩ : {ℓ : LF} → Tr ℓ → Set
  IsLim (lim _ _) = ⊤
  IsLim _         = ⊥
  IsΩ (Ω _ _) = ⊤
  IsΩ _       = ⊥

  flat-in : IsΩ (Upc (tw 1) one β (Ωt-nz (tw 1)) (Ωt (h₁ one)))
  flat-in = tt

  note-cof : E.cof (E.ψ u₁ (E.ψ Ω₁ᵗ Ω₁ᵗ ∷ []) ∷ []) ≡ E.cΩ []
  note-cof = refl
```
