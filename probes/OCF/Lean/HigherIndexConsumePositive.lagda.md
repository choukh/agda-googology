# 实际消费者的统一正性与纯后缀下界

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumePositive where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; ≤l; l≤)
open import OCF.Lean.Fold1Base using (mul-≤; ≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
import OCF.Lean.Fold1If as I
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.LHRecFl using (flL)
import OCF.Lean.LHRecLeg as L
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.HigherIndexClassIf using (U)
open import OCF.Lean.HigherIndexFoldIf using (k; Source)
open import OCF.Lean.HigherIndexSupportIf using (next)
open import OCF.Lean.HigherIndexSupportSource using (Supported)
open import OCF.Lean.HigherIndexConsumeCode using (code; legal-next; pure)
open import OCF.Lean.HigherIndexConsumeRun

positive : ∀ β lb B lB a p → hs hz ≤ᵛ run β lb B lB a p
positive β lb B lB hz p = s≤s z≤
positive β lb B lB (hs a) p = ≤l 0 (positive β lb B lB a p)
positive β lb B lB (hl f) p = ≤l 0 (positive β lb B lB (f 0) (p 0))
positive β lb B lB (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p
positive β lb B lB (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p = ≤l 0
  (positive (hs e) le B lB (f e) (p e (⊞-fst β (C.leg (hs hz))) le))
  where
  e = β ⊞ C.leg (hs hz)
  le : LgB e
  le = Lg-⊞ β (C.leg (hs hz)) lb (C.Lg-leg (hs hz))
positive β lb B lB (hΩ (inj₁ _ , inj₂ _) f) p = ≤l 0
  (positive β lb (hs e) le (f e) (p e ad))
  where
  e = high-coordinate B (hs hz)
  le : LgB e
  le = Lg-⊞ B _ lB (L.Lg-leg k (flL k ⊞ pure U (C.leg (hs hz))))
  ad = LHRecIf.adm-sh L.J₁ k {W = (tt , β) , B} (flL k ⊞ pure U (C.leg (hs hz))) ((tt , lb) , lB)
positive β lb B lB (hΩ (inj₂ c , κ) f) (ev , p) = ≤l 0
  (positive (next c κ β e ad) (legal-next c κ β lb e ad) B lB (f e) (p e ad))
  where
  encoded = code c κ β lb (hs hz)
  e = proj₁ encoded
  ad = proj₂ encoded

-- Pure记录真实源树只含0/s/ℕ，而不要求具体嵌入函数名定义相等。
data Pure : Cd → HB Source → Set where
  pz : Pure hz hz
  ps : ∀ {d a} → Pure d a → Pure (hs d) (hs a)
  pl : ∀ {f g} → (∀ n → Pure (f n) (g n)) → Pure (hl f) (hl g)

import OCF.Lean.Fold1Fold as Old
old-act : Cd → Cd
old-act d = Old.Φ (hs hz) tt hz (hsuc hself) (tt , hz) (up d)

add-mono : ∀ {a b c d : Cd} → a ≤ᵛ b → c ≤ᵛ d → a ⊞ c ≤ᵛ b ⊞ d
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)
mul-partial : ∀ {a b : Cd} → a ≤ᵛ b → ∀ n → I.mul a n ≤ᵛ Ops.partial S⊥ (λ _ → b) n
mul-partial p zero = p
mul-partial p (suc n) = add-mono (mul-partial p n) p

pure-suffix : ∀ {d a} → Pure d a → ∀ β lb B lB A p →
  old-act d ≤ᵛ run β lb B lB (A ⊞ a) p
pure-suffix pz β lb B lB A p = positive β lb B lB A p
pure-suffix (ps q) β lb B lB A p = l≤ (λ n → ≤l n (mul-partial (pure-suffix q β lb B lB A p) n))
pure-suffix (pl q) β lb B lB A p = l≤ (λ n → ≤l n (pure-suffix (q n) β lb B lB A (p n)))
```
