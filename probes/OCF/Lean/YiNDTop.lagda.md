# 根表可变、孩子表固定时的 Ω 树模拟
验收文件；来源 YiMTRel.upA/upS/topΩ，孩子的递归改用 YiVTRel.A/S。
根表任意，孩子字面取 rbᶻ；对左项为零的分支，不使用根上的表格。
前提的规范实例为 YiNDBridge.rB1，实际应用见 YiNDAccept.beta2-R。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNDTop where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; kp⁼; node⁺; nodeLe)
open import OCF.Lean.YiTBRow using (Rb; RbS; ψ; mono)
open import OCF.Lean.YiNRHit using (NoΩ)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
open import OCF.Lean.YiBROps
open import OCF.Lean.YiBRFold using (W→L; B₀-R; iterR; node0; nodeLe0; kp-R)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiMTRel using (U0; u0)
import OCF.Lean.YiVTRel as VR
upA : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β x)) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
    × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β x)) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
upA {k′ = k′} {h′} {ε = ε} {ρ} (eΩ rk rwc rc) B B′ rB β rβ rn {x′ = F.up _ c′ y′ e′} (u0 z y e) (iu (iz , (rcc , ry , _))) =
  VR.A (rc z c′ rcc) (λ i u → B i (inc z u)) (F.dW k′ h′ ε ρ B′ c′ F.zero)
    (λ i i′ w w′ rw → rB i i′ (inc z w) (F.inb c′ w′) (wincΩ rcc rw)) β rβ rn ry

upS : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → ∀ {j j′} {v : j ≤ k} {w′ : F._≤_ j′ (F.Ωₗ k′ h′)} → RelW (ink {h = h} v) w′
    → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT j j′ (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B j (ink v) β x)) (F.ψs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
    × RelD j j′ (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B j (ink v) β x)) (F.nzs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
upS {k′ = k′} {h′} {ε = ε} {ρ} (eΩ rk rwc rc) B B′ rB (wink rv) β rβ rn {x′ = F.up _ c′ y′ e′} (u0 z y e) (iu (iz , (rcc , ry , _))) =
  VR.S (rc z c′ rcc) (λ i u → B i (inc z u)) (F.dW k′ h′ ε ρ B′ c′ F.zero)
    (λ i i′ w w′ rw → rB i i′ (inc z w) (F.inb c′ w′) (wincΩ rcc rw)) (∙-R rv (rwc z c′ rcc)) β rβ rn ry

topΩ : ∀ {k h k′ h′ o ε ρ} {tb : RbS (sΩ k) h} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
     → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {t : Pos⁼ k} {g : Br (nd (sΩ k) h) (inj₁ t) → Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)}
     → ((z : Br (nd (sΩ k) h) (inj₁ t)) → U0 (g z)) → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) (Ω (inj₁ t) g) x′
     → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
     × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o (tb , λ c → rbᶻ (h c)) B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
topΩ {k} {h} {k′} {h′} {o} {ε} {ρ} {tb} re B B′ rB β rβ rn {t} {g} {x′ = F.Ω p′ g′} uz (iw (rp , rg)) =
  node0 (kp ℓ o p (z≤ ℓ)) G sR
    (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
       (λ n → proj₁ (upA re B B′ rB β rβ rn (uz _) (rg _ _ (ch n)))) (λ n → proj₂ (upA re B B′ rB β rβ rn (uz _) (rg _ _ (ch n))))
     , dt (proj₂ (upA re B B′ rB β rβ rn (uz _) (rg _ _ (ch zero))) , dl))
  where
  ℓ : L
  ℓ = nd (sΩ k) h
  ℓ′ : F.L
  ℓ′ = F.Ωₗ k′ h′
  p : Pos ℓ
  p = inj₁ t
  rl : RelL ℓ ℓ′
  rl = E→L re
  G : Br ℓ p → Tr⁺ zero
  G z = ψ ℓ o (tb , λ c → rbᶻ (h c)) B zero (z≤ ℓ) β (g z)
  sR : Br ℓ p → Br ℓ p
  sR z = fromBr ℓ p (proj₁ (ψ ℓ o (tb , λ c → rbᶻ (h c)) B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
  s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
  s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
              (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
  rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
  ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
  ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
         (λ z z′ rz → fromBr-R rl p p′ rp
            (proj₁ (upS re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (uz z) (rg z z′ rz))))
```
