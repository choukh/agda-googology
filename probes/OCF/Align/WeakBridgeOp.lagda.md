# 不带高度的树接上带高度的树 (二″: 右边的运算, 加法)

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 分文件只为编译的内存.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeOp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; Ωˢ)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo)
import OCF.Free.Tree as FT
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; zl; sl; ll; ĉl)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel using (⌜_⌝; Emp; out-intoU; out-intoC; out-intoV; cv-into)
open import OCF.Align.LadderInfNat using (HSℕ)
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeRel
open import OCF.Align.WeakBridgeC
open I using (q0; qs; ql; qi; qŝ; qĉ; qclo; qwk; qΩ) renaming (omk to qmk; _⊞_ to _⊞_)
```


## §6 右边的运算

```agda
R-ιQ : ∀ {M B B′} (s : B ◃ B′) {A π φ χ} {x : O A π} {y : QQ B φ χ} → C M x y → C M x (I.ι s y)
R-ιQ s cz = cz
R-ιQ s (cs c D) = cs c (R-ιQ s D)
R-ιQ s (cl h) = cl (λ n → R-ιQ s (h n))
R-ιQ s (cwl D) = cwl (R-ιQ s D)
R-ιQ s (cvl D) = cvl (R-ιQ s D)
R-ιQ s (cwr D) = cwr (R-ιQ s D)
R-ιQ s (cdr {y = y₀} D) = R-ιQ s {y = y₀} D
R-ιQ s (cm r l dk lr E D) = cm r (oι s ∷ᵒ l) dk lr (≃-ι s E) (R-ιQ s D)
R-ιQ s (cml r cv l d E D) = cml r cv (oι s ∷ᵒ l) d (≃-ι s E) (R-ιQ s D)
R-ιQ s (ci r dk prem) = ci r dk (λ ξ em z ẑ l → R-ιQ s (prem ξ em z ẑ l))
R-ιQ {M} s {φ = φ} {χ = χ} (cΩ r q {h = h} {f = f} dk e₂ q₂ c prem) =
  cΩ r (FT.<◃ q s) dk e₂ q₂ c (λ ξ ξ̂ ζ cv z ẑ l →
    subst (λ u → C M (h ξ (intoU r z)) (I.ι s (f ξ̂ ζ (I.intoU (<→◃ q) u)))) (sym (outU-into (<→◃ (FT.<◃ q s)) ẑ)) (R-ιQ s (prem ξ ξ̂ ζ cv z ẑ l)))
R-ιQ s (cŝ n ec rt rg) = cŝ n ec (R-ιQ s rt) (λ η e e′ → R-ιQ s (rg η e e′))
R-ιQ s (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-ιQ s ro) (λ η e e′ → R-ιQ s (rg η e e′))
R-ιQ s (ccl c rt rg) = ccl c (R-ιQ s rt) (λ η e → R-ιQ s (rg η e))

R-trQ  : ∀ {M a b} (d : a ≅ᴵ b) {A π φ χ} {x : O A π} {y : QQ a φ χ} → C M x y → C M x (I.trQ d y)
R-tr⁻Q : ∀ {M a b} (d : a ≅ᴵ b) {A π φ χ} {x : O A π} {y : QQ b φ χ} → C M x y → C M x (I.tr⁻Q d y)
R-bkQ  : ∀ {M j a b} (q : j <ᴵ a) (d : a ≅ᴵ b) {A ξ φ χ} {z : O A ξ} {ẑ : QQ (I.repQ (I.resQ {0} q d)) φ χ} → C M z ẑ → C M z (I.backQ (I.resQ {0} q d) ẑ)
R-bk⁻Q : ∀ {M j a b} (q : j <ᴵ b) (d : a ≅ᴵ b) {A ξ φ χ} {z : O A ξ} {ẑ : QQ (I.repQ (I.res⁻Q {0} q d)) φ χ} → C M z ẑ → C M z (I.backQ (I.res⁻Q {0} q d) ẑ)

R-trQ d cz = cz
R-trQ d (cs c D) = cs c (R-trQ d D)
R-trQ d (cl h) = cl (λ n → R-trQ d (h n))
R-trQ d (cwl D) = cwl (R-trQ d D)
R-trQ d (cvl D) = cvl (R-trQ d D)
R-trQ d (cwr D) = cwr (R-trQ d D)
R-trQ (s≅ d) (cdr {r = zero} D) = cdr (R-trQ (s≅ d) D)
R-trQ (l≅ h) (cdr {r = self n} D) = cdr (R-trQ (l≅ h) D)
R-trQ d (cm r l dk lr E D) = cm r (otr d ∷ᵒ l) dk lr (≃-trQ d E) (R-trQ d D)
R-trQ d (cml r cv l p E D) = cml r cv (otr d ∷ᵒ l) p (≃-trQ d E) (R-trQ d D)
R-trQ d (ci r dk prem) = ci r dk (λ ξ em z ẑ l → R-trQ d (prem ξ em z ẑ l))
R-trQ {M} d (cΩ r q {h = h} {f = f} dk e₂ q₂ c prem) =
  cΩ r (I.ltQ (I.resQ q d)) (≈-trans dk (c⁺-≈ (I.eqQ (I.resQ q d)))) (≅ᴵ-trans (≅ᴵ-sym (I.eqQ (I.resQ q d))) e₂) q₂ c (λ ξ ξ̂ ζ cv z ẑ l →
    subst (λ u → C M (h ξ (intoU r z)) (I.trQ d (f ξ̂ ζ (I.intoU (<→◃ q) (I.backQ (I.resQ q d) u))))) (sym (outU-into (<→◃ (I.ltQ (I.resQ q d))) ẑ))
          (R-trQ d (prem ξ ξ̂ ζ cv z _ (intoL (<→◃ q₂) (R-bkQ q d (outL (<→◃ q₂) l))))))
R-trQ d (cŝ n ec rt rg) = cŝ n ec (R-trQ d rt) (λ η e e′ → R-trQ d (rg η e e′))
R-trQ d (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-trQ d ro) (λ η e e′ → R-trQ d (rg η e e′))
R-trQ d (ccl c rt rg) = ccl c (R-trQ d rt) (λ η e → R-trQ d (rg η e))

R-tr⁻Q d cz = cz
R-tr⁻Q d (cs c D) = cs c (R-tr⁻Q d D)
R-tr⁻Q d (cl h) = cl (λ n → R-tr⁻Q d (h n))
R-tr⁻Q d (cwl D) = cwl (R-tr⁻Q d D)
R-tr⁻Q d (cvl D) = cvl (R-tr⁻Q d D)
R-tr⁻Q d (cwr D) = cwr (R-tr⁻Q d D)
R-tr⁻Q (s≅ d) (cdr {r = zero} D) = cdr (R-tr⁻Q (s≅ d) D)
R-tr⁻Q (l≅ h) (cdr {r = self n} D) = cdr (R-tr⁻Q (l≅ h) D)
R-tr⁻Q d (cm r l dk lr E D) = cm r (otr⁻ d ∷ᵒ l) dk lr (≃-tr⁻Q d E) (R-tr⁻Q d D)
R-tr⁻Q d (cml r cv l p E D) = cml r cv (otr⁻ d ∷ᵒ l) p (≃-tr⁻Q d E) (R-tr⁻Q d D)
R-tr⁻Q d (ci r dk prem) = ci r dk (λ ξ em z ẑ l → R-tr⁻Q d (prem ξ em z ẑ l))
R-tr⁻Q {M} d (cΩ r q {h = h} {f = f} dk e₂ q₂ c prem) =
  cΩ r (I.ltQ (I.res⁻Q q d)) (≈-trans dk (c⁺-≈ (I.eqQ (I.res⁻Q q d)))) (≅ᴵ-trans (≅ᴵ-sym (I.eqQ (I.res⁻Q q d))) e₂) q₂ c (λ ξ ξ̂ ζ cv z ẑ l →
    subst (λ u → C M (h ξ (intoU r z)) (I.tr⁻Q d (f ξ̂ ζ (I.intoU (<→◃ q) (I.backQ (I.res⁻Q q d) u))))) (sym (outU-into (<→◃ (I.ltQ (I.res⁻Q q d))) ẑ))
          (R-tr⁻Q d (prem ξ ξ̂ ζ cv z _ (intoL (<→◃ q₂) (R-bk⁻Q q d (outL (<→◃ q₂) l))))))
R-tr⁻Q d (cŝ n ec rt rg) = cŝ n ec (R-tr⁻Q d rt) (λ η e e′ → R-tr⁻Q d (rg η e e′))
R-tr⁻Q d (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-tr⁻Q d ro) (λ η e e′ → R-tr⁻Q d (rg η e e′))
R-tr⁻Q d (ccl c rt rg) = ccl c (R-tr⁻Q d rt) (λ η e → R-tr⁻Q d (rg η e))

R-bkQ zero (s≅ d) l = R-tr⁻Q d l
R-bkQ (suc q) (s≅ d) l = R-bkQ q d l
R-bkQ (lim n q) (l≅ h) l = R-bkQ q (h n) l

R-bk⁻Q zero (s≅ d) l = R-trQ d l
R-bk⁻Q (suc q) (s≅ d) l = R-bk⁻Q q d l
R-bk⁻Q (lim n q) (l≅ h) l = R-bk⁻Q q (h n) l

R-ap₁ : ∀ {M a b} (o : Op a b) {A π φ χ} {x : O A π} {y : QQ a φ χ} → C M x y → C M x (ap₁ o y)
R-ap₁ (oι s) D = R-ιQ s D
R-ap₁ (otr d) D = R-trQ d D
R-ap₁ (otr⁻ d) D = R-tr⁻Q d D

R-ap : ∀ {M a b} (l : Ops a b) {A π φ χ} {x : O A π} {y : QQ a φ χ} → C M x y → C M x (ap l y)
R-ap []ᵒ D = D
R-ap (o ∷ᵒ l) D = R-ap₁ o (R-ap l D)
```

## §7 `≃` 进关系

```agda
Tᴿ : ∀ {M A π B φ φ′ χ χ′} {x : O A π} {y : QQ B φ χ} {y′ : QQ B φ′ χ′} → C M x y → y ≃ y′ → C M x y′
Tᴿ D ≃id = D
Tᴿ D (≃wr E) = cwr (Tᴿ D E)
Tᴿ D (≃mr E) = cdr (Tᴿ D E)
Tᴿ (cwl D) E = cwl (Tᴿ D E)
Tᴿ (cvl D) E = cvl (Tᴿ D E)
Tᴿ (cm r l dk lr E₀ D) E = cm r l dk lr (≃-trans E₀ E) (Tᴿ D E)
Tᴿ (cml r cv l p E₀ D) E = cml r cv l p (≃-trans E₀ E) (Tᴿ D E)
Tᴿ (cwr D) (≃wl E) = Tᴿ D E
Tᴿ (cdr D) (≃ml E) = Tᴿ D E
Tᴿ cz ≃z = cz
Tᴿ (cs c D) (≃s f E) = cs (λ g m e → c g m (f e)) (Tᴿ D E)
Tᴿ (cl h) (≃l H) = cl (λ n → Tᴿ (h n) (H n))
Tᴿ (ci r dk prem) (≃i H) = ci r dk (λ ξ em z ẑ l → Tᴿ (prem ξ em z ẑ l) (H ẑ))
Tᴿ (cΩ r q dk e₂ q₂ c prem) (≃Ω .q f H) = cΩ r q dk e₂ q₂ (λ g m e → c g m (f e)) (λ ξ ξ̂ ζ cv z ẑ l → Tᴿ (prem ξ ξ̂ ζ cv z ẑ l) (H ξ̂ ζ _))
Tᴿ (cŝ n ec rt rg) (≃ŝ E H) = cŝ n ec (Tᴿ rt E) (λ η e e′ → Tᴿ (rg η e e′) (H η e′))
Tᴿ (cĉ ec dz dg ro rg) (≃ĉ E H) = cĉ ec dz dg (Tᴿ ro E) (λ η e e′ → Tᴿ (rg η e e′) (H η e′))
Tᴿ (ccl c rt rg) (≃c f E H) = ccl (λ g m e → c g m (f e)) (Tᴿ rt E) (λ η e → Tᴿ (rg η e) (H η))
```

## §8 加法

```agda
R⊕ : ∀ {M A φW φ̂W π B φ χW χ} {W : O A φW} {Ŵ : QQ B φ̂W χW} {t : O A π} {t̂ : QQ B φ χ} → CvL φW φ̂W → C M W Ŵ → C M t t̂ → C M (W ⊕ t) (Ŵ ⊞ t̂)
R⊕ cW rW cz = cwl (cwr rW)
R⊕ cW rW (cs c r) = cs (cvL-∪ cW c) (R⊕ cW rW r)
R⊕ cW rW (cl h) = cl (λ n → R⊕ cW rW (h n))
R⊕ cW rW (cwl r) = cwl (R⊕ cW rW r)
R⊕ cW rW (cvl r) = cvl (R⊕ cW rW r)
R⊕ cW rW (cwr r) = cwr (R⊕ cW rW r)
R⊕ cW rW (cdr {y = y₀} r) = R⊕ {t̂ = y₀} cW rW r
R⊕ cW rW (cm {x = x₀} r l dk lr E D) = R⊕ {t = x₀} cW rW D
R⊕ cW rW (cml {x = x₀} r cv l p E D) = R⊕ {t = x₀} cW rW D
R⊕ cW rW (ci r dk prem) = ci r dk (λ ξ em z ẑ l → cwl (R⊕ cW rW (prem ξ em z ẑ l)))
R⊕ cW rW (cΩ r q dk e₂ q₂ c prem) = cΩ r q dk e₂ q₂ (cvL-∪ cW c) (λ ξ ξ̂ ζ cv z ẑ l → cwl (cwr (R⊕ cW rW (prem ξ ξ̂ ζ cv z ẑ l))))
R⊕ {A = Lv.zero} cW rW (cŝ () ec rt rg)
R⊕ {A = Lv.suc _} cW rW (cŝ n ec rt rg) = cŝ tt ec (R⊕ cW rW rt) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ {A = Lv.lim _} cW rW (cŝ n ec rt rg) = cŝ tt ec (R⊕ cW rW rt) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ {A = Lv.lc _ _ _} cW rW (cŝ n ec rt rg) = cŝ tt ec (R⊕ cW rW rt) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ cW rW (cĉ ec dz dg ro rg) = cĉ ec dz dg (R⊕ cW rW ro) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ cW rW (ccl cv rt rg) = cwr (ccl (cvL-∪ cW cv) (cwr (R⊕ cW rW rt)) (λ η e → cwl (cwr (R⊕ cW rW (rg η e)))))

rep-C : ∀ {M A ρ B φ χ} {y : O A ρ} {ŷ : QQ B φ χ} → CvL ρ φ → C M y ŷ → ∀ n → C M (repᵒ y n) (I.repᵠ ŷ n)
rep-C c r zero = cz
rep-C c r (suc zero) = cwl (cwl r)
rep-C {ŷ = ŷ} c r (suc (suc n)) = cwl (Tᴿ (R⊕ c r (rep-C c r (suc n))) (rep≃ ŷ (suc n)))
```
