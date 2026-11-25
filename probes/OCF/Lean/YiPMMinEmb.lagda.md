# 最小表实例: Emb

参数化（工程）的最小表实例；验收文件。来源 `YiVTEmb`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinEmb where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inl; inlu; inb; _∙_; Ev; Rt; Ev-tw; Rt-tw; way; caseW-ind; emb; emb-nz)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read; read-+; plus≽; ◃→≺)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (NL; n0; n+; nω)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁; G; nl-↑)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (IsLim)
open import OCF.Lean.YiDropRow using (ι₀≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≺→s≼) renaming (+-mono to +ᵛ-mono)

data Em1 : (ℓ : LF) → Tr ℓ → Set where
  e0 : Em1 zero (suc zero)
  eS : ∀ {a y e} → Em1 a y → Em1 (suc a) (up zero tt y e)
  eL : ∀ {g} n {y e} → Em1 (g n) y → Em1 (lim g) (up zero n y e)

emb-Em : ∀ {ℓ} → NL ℓ → (ε : Ev ℓ) → ∀ {k} (v : k ≤ ℓ) {y nz} → Em1 k y → Em1 ℓ (emb ℓ ε v y nz)
emb-Em f      ε self      em = em
emb-Em (n+ f) ε (ins v)   em = eS (emb-Em f ε v em)
emb-Em (nω f) ε (inl n v) em = eL n (emb-Em (f n) (ε n) v em)
emb-Em (nω f) ε (inlu vs) em = eL zero (emb-Em (f zero) (ε zero) (vs zero) em)

em-fold : ∀ {ℓ} → NL ℓ → ∀ {t} → Em1 ℓ t → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (w : zero ≤ ℓ)
  (b : Tr zero) (nb : zero ⊢ zero ◃ b) → ψs ℓ ε ρ B zero w b nb t ≡ next b nb
em-fold n0     e0      ε ρ B self    b nb = refl
em-fold (n+ f) (eS em) ε ρ B (ins w) b nb = em-fold f em ε ρ _ w b nb
em-fold (nω f) (eL n em) ε (ρc , R) B (inlu ws) b nb = em-fold (f n) em (ε n) (ρc n) _ (ws n) b nb
em-fold (nω f) (eL {g} n em) ε (ρc , R) B (inl m w) b nb =
  caseW-ind (λ Z → Z ≡ next b nb) (way g R n m)
    (λ v → em-fold (f m) (emb-Em (f m) (ε m) v em) (ε m) (ρc m) _ w b nb)
    (λ v → em-fold (f n) em (ε n) (ρc n) _ (w ∙ v) b nb)

next1≼ : (b : Tr zero) (nb : zero ⊢ zero ◃ b) → read (next (suc zero) ◃s) ≼ read (next b nb)
next1≼ b nb = l≼ (λ n → ≼l n (it n))
  where
  it : ∀ n → read (iter (suc zero +_) (suc zero) n) ≼ read (iter (b +_) b n)
  it zero    = ≺→s≼ (◃→≺ nb)
  it (suc n) = ≼-trans (≅→≼ (read-+ (suc zero) (iter (suc zero +_) (suc zero) n)))
    (≼-trans (+ᵛ-mono (≺→s≼ (◃→≺ nb)) (it n)) (≅→≼ (L.≅-sym (read-+ b (iter (b +_) b n)))))

rowT : (B : Base (tw 1)) (c : Tr zero) (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) (x : Tr zero) → Tr zero
rowT B c w b nb x = ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (up zero x (Ωt (h₁ x)) (Ωt-nz (h₁ x)))

rowG : (B : Base (tw 1)) (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) (x : Tr zero)
  → read (G x) ≼ read (rowT B c w b nb x)
rowG B c@(lim f a) tt w b nb zero =
  subst (λ Z → read (G zero) ≼ read Z)
    (sym (em-fold (nl-↑ c) (emb-Em (nl-↑ c) (proj₂ (proj₂ (Ev-tw 1) c)) (z≤ᶠ (h₁ c)) e0)
            (proj₂ (proj₂ (Ev-tw 1) c)) (proj₂ (Rt-tw 1) c) _ w b nb))
    (next1≼ b nb)
rowG B (lim f a) tt w b nb (suc x)   = plus≽ b (ι zero (G (suc x))) (≅→≼ (L.≅-sym (ι₀≅ (G (suc x)))))
rowG B (lim f a) tt w b nb (lim g d) = plus≽ b (ι zero (G (lim g d))) (≅→≼ (L.≅-sym (ι₀≅ (G (lim g d)))))
rowG B (lim f a) tt w b nb (Ω () _)
rowG B (lim f a) tt w b nb (up _ () _ _)
```
