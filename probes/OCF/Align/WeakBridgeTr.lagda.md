# 不带高度的树接上带高度的树 (二′): 关系沿左边的 `≈` 搬运

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 从 [WeakBridgeRel](WeakBridgeRel.lagda.md) 分出来, 只为编译的内存.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeTr where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel using (out-intoU)
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeRel
open import OCF.Align.WeakBridgeC
open CR using (rmk)
```

## §9 左边的搬运

与 [GuardCertRel](GuardCertRel.lagda.md) 的 §4 同一个递归: 对 `≈` 与推导字典序.

```agda
BkC : ∀ {k a b} {r : k < a} → RestrO r b → Set
BkC w = ∀ {M ξ B φ χ} {z : O (repO w) ξ} {ẑ : QQ B φ χ} → C M z ẑ → C M (backO w z) ẑ

Cf-trO  : ∀ {M A A′ π B φ χ} (e : A ≈ A′) {x : O A π} {y : QQ B φ χ} → C M x y → C M (trO e x) y
Cf-tr⁻O : ∀ {M A A′ π B φ χ} (e : A ≈ A′) {x : O A′ π} {y : QQ B φ χ} → C M x y → C M (tr⁻O e x) y
Cf-bk   : ∀ {k A A′} (q : k < A) (e : A ≈ A′) → BkC (resO q e)
Cf-bk⁻  : ∀ {k A A′} (q : k < A′) (e : A ≈ A′) → BkC (res⁻O q e)
Cf-trC  : ∀ {M k A A′ ξ B φ χ} (P : Cp k A) (e : A ≈ A′) (z : Vc A P ξ) {ẑ : QQ B φ χ} → C M (outC P z) ẑ → C M (outC (posC (trC P e z)) (valC (trC P e z))) ẑ
Cf-tr⁻C : ∀ {M k A A′ ξ B φ χ} (P : Cp k A′) (e : A ≈ A′) (z : Vc A′ P ξ) {ẑ : QQ B φ χ} → C M (outC P z) ẑ → C M (outC (posC (tr⁻C P e z)) (valC (tr⁻C P e z))) ẑ
Cf-trV  : ∀ {M k A A′ ξ B φ χ} (R : Strict k A) (e : A ≈ A′) (z : Vs A R ξ) {ẑ : QQ B φ χ} → C M (outV R z) ẑ → C M (outV (posW (trV R e z)) (valW (trV R e z))) ẑ
Cf-tr⁻V : ∀ {M k A A′ ξ B φ χ} (R : Strict k A′) (e : A ≈ A′) (z : Vs A′ R ξ) {ẑ : QQ B φ χ} → C M (outV R z) ẑ → C M (outV (posW (tr⁻V R e z)) (valW (tr⁻V R e z))) ẑ

Cf-trO e cz = cz
Cf-trO e (cs c r) = cs c (Cf-trO e r)
Cf-trO e (cl h) = cl (λ n → Cf-trO e (h n))
Cf-trO e (cwl r) = cwl (Cf-trO e r)
Cf-trO e (cvl r) = cvl (Cf-trO e r)
Cf-trO e (cwr r) = cwr (Cf-trO e r)
Cf-trO e (cdr r) = cdr (Cf-trO e r)
Cf-trO e (cm {R = R} {z = z} r l dk lr E D) with trV R e z | Cf-trV R e z (outL r lr) | CR.trV-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = cm r l dk′ (intoL r l′) E (Cf-trO e D)
Cf-trO e (cml {m₀ = m₀} {R = R} {z = z} zero cv l (rmk zero dk l₀ iv m) E D) with trV R e z | CR.R-trV R e z l₀ | CR.iv-trV R e z iv | CR.trV-≈ R e z dk
... | restrV R′ u z′ | l′ | iv′ | dk′ = cml {m₀ = m₀} zero cv l (rmk zero dk′ l′ iv′ (CR.R-trO e m)) E (Cf-trO e D)
Cf-trO e (cml {m₀ = m₀} {R = R} {z = z} (self n) cv l (rmk (self .n) dk l₀ iv m) E D) with trV R e z | CR.R-trV R e z l₀ | CR.trV-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = cml {m₀ = m₀} (self n) cv l (rmk (self n) dk′ l′ tt (CR.R-trO e m)) E (Cf-trO e D)
Cf-trO {M} e (ci r {h = h₁} {f = f} dk prem) =
  ci (ltO (resO r e)) (≈-trans (≈-sym (eqO (resO r e))) dk)
     (λ ξ em z ẑ l → Cf-trO e (subst (λ u → C M (h₁ ξ (intoU r (backO (resO r e) u))) (f ẑ)) (sym (out-intoU (ltO (resO r e)) z))
                                      (prem ξ em _ ẑ (CR.R-bk r e l))))
Cf-trO {M} e (cΩ r q {h = h₁} {f = f} dk e₂ q₂ c prem) =
  cΩ (ltO (resO r e)) q (≈-trans (≈-sym (eqO (resO r e))) dk) e₂ q₂ c
     (λ ξ ξ̂ ζ cv z ẑ l → Cf-trO e (subst (λ u → C M (h₁ ξ (intoU r (backO (resO r e) u))) (f ξ̂ ζ (I.intoU (<→◃ q) ẑ))) (sym (out-intoU (ltO (resO r e)) z))
                                      (prem ξ ξ̂ ζ cv _ ẑ (intoL (<→◃ q₂) (Cf-bk r e (outL (<→◃ q₂) l))))))
Cf-trO e (cŝ n ec rt rg) = cŝ (nz-≈ e n) ec (Cf-trO e rt) (λ η d d′ → Cf-trO e (rg η d d′))
Cf-trO e (cĉ ec dz dg ro rg) = cĉ ec dz dg (Cf-trO e ro) (λ η d d′ → Cf-trO e (rg η d d′))
Cf-trO e (ccl {P = P} c rt rg) with ≈-moveᴷ e P
... | viaᴷ d P′ u = ccl c (Cf-trO e rt) (λ η d′ → Cf-trO e (rg η d′))

Cf-tr⁻O e cz = cz
Cf-tr⁻O e (cs c r) = cs c (Cf-tr⁻O e r)
Cf-tr⁻O e (cl h) = cl (λ n → Cf-tr⁻O e (h n))
Cf-tr⁻O e (cwl r) = cwl (Cf-tr⁻O e r)
Cf-tr⁻O e (cvl r) = cvl (Cf-tr⁻O e r)
Cf-tr⁻O e (cwr r) = cwr (Cf-tr⁻O e r)
Cf-tr⁻O e (cdr r) = cdr (Cf-tr⁻O e r)
Cf-tr⁻O e (cm {R = R} {z = z} r l dk lr E D) with tr⁻V R e z | Cf-tr⁻V R e z (outL r lr) | CR.tr⁻V-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = cm r l dk′ (intoL r l′) E (Cf-tr⁻O e D)
Cf-tr⁻O e (cml {m₀ = m₀} {R = R} {z = z} zero cv l (rmk zero dk l₀ iv m) E D) with tr⁻V R e z | CR.R-tr⁻V R e z l₀ | CR.iv-tr⁻V R e z iv | CR.tr⁻V-≈ R e z dk
... | restrV R′ u z′ | l′ | iv′ | dk′ = cml {m₀ = m₀} zero cv l (rmk zero dk′ l′ iv′ (CR.R-tr⁻O e m)) E (Cf-tr⁻O e D)
Cf-tr⁻O e (cml {m₀ = m₀} {R = R} {z = z} (self n) cv l (rmk (self .n) dk l₀ iv m) E D) with tr⁻V R e z | CR.R-tr⁻V R e z l₀ | CR.tr⁻V-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = cml {m₀ = m₀} (self n) cv l (rmk (self n) dk′ l′ tt (CR.R-tr⁻O e m)) E (Cf-tr⁻O e D)
Cf-tr⁻O {M} e (ci r {h = h₁} {f = f} dk prem) =
  ci (ltO (res⁻O r e)) (≈-trans (≈-sym (eqO (res⁻O r e))) dk)
     (λ ξ em z ẑ l → Cf-tr⁻O e (subst (λ u → C M (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f ẑ)) (sym (out-intoU (ltO (res⁻O r e)) z))
                                      (prem ξ em _ ẑ (CR.R-bk⁻ r e l))))
Cf-tr⁻O {M} e (cΩ r q {h = h₁} {f = f} dk e₂ q₂ c prem) =
  cΩ (ltO (res⁻O r e)) q (≈-trans (≈-sym (eqO (res⁻O r e))) dk) e₂ q₂ c
     (λ ξ ξ̂ ζ cv z ẑ l → Cf-tr⁻O e (subst (λ u → C M (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f ξ̂ ζ (I.intoU (<→◃ q) ẑ))) (sym (out-intoU (ltO (res⁻O r e)) z))
                                      (prem ξ ξ̂ ζ cv _ ẑ (intoL (<→◃ q₂) (Cf-bk⁻ r e (outL (<→◃ q₂) l))))))
Cf-tr⁻O e (cŝ n ec rt rg) = cŝ (nz-≈ (≈-sym e) n) ec (Cf-tr⁻O e rt) (λ η d d′ → Cf-tr⁻O e (rg η d d′))
Cf-tr⁻O e (cĉ ec dz dg ro rg) = cĉ ec dz dg (Cf-tr⁻O e ro) (λ η d d′ → Cf-tr⁻O e (rg η d d′))
Cf-tr⁻O e (ccl {P = P} c rt rg) with ≈-moveᴷ (≈-sym e) P
... | viaᴷ d P′ u = ccl c (Cf-tr⁻O e rt) (λ η d′ → Cf-tr⁻O e (rg η d′))

Cf-bk Lv.zero (Lv.s≈ e) = Cf-tr⁻O e
Cf-bk (Lv.suc r) (Lv.s≈ e) with resO r e | Cf-bk r e
... | restrO d m t b | H = H
Cf-bk (Lv.lim n r) (Lv.l≈ h) with resO r (h n) | Cf-bk r (h n)
... | restrO d m t b | H = H
Cf-bk (Lv.fst r) (Lv.o≈ d′ e h) with resO r e | Cf-bk r e
... | restrO d m t b | H = H
Cf-bk (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with resO r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η)) | Cf-bk r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η))
... | restrO d m t b | H = H

Cf-bk⁻ Lv.zero (Lv.s≈ e) = Cf-trO e
Cf-bk⁻ (Lv.suc r) (Lv.s≈ e) with res⁻O r e | Cf-bk⁻ r e
... | restrO d m t b | H = H
Cf-bk⁻ (Lv.lim n r) (Lv.l≈ h) with res⁻O r (h n) | Cf-bk⁻ r (h n)
... | restrO d m t b | H = H
Cf-bk⁻ (Lv.fst r) (Lv.o≈ d′ e h) with res⁻O r e | Cf-bk⁻ r e
... | restrO d m t b | H = H
Cf-bk⁻ (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with res⁻O r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η)) | Cf-bk⁻ r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η))
... | restrO d m t b | H = H

Cf-trC Lv.self e z l = Cf-trO e l
Cf-trC (Lv.suc P) (Lv.s≈ e) z l with trC P e z | Cf-trC P e z l
... | restrC Q u z′ | l′ = l′
Cf-trC (Lv.lim n P) (Lv.l≈ h) z l with trC P (h n) z | Cf-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
Cf-trC (Lv.fst P) (Lv.o≈ d e h) z l with trC P e z | Cf-trC P e z l
... | restrC Q u z′ | l′ = l′
Cf-trC (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | Cf-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

Cf-tr⁻C Lv.self e z l = Cf-tr⁻O e l
Cf-tr⁻C (Lv.suc P) (Lv.s≈ e) z l with tr⁻C P e z | Cf-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻C (Lv.lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | Cf-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻C (Lv.fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | Cf-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻C (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | Cf-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

Cf-trV (st-suc P) (Lv.s≈ e) z l with trC P e z | Cf-trC P e z l
... | restrC Q u z′ | l′ = l′
Cf-trV (st-lim n P) (Lv.l≈ h) z l with trC P (h n) z | Cf-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
Cf-trV (st-fst P) (Lv.o≈ d e h) z l with trC P e z | Cf-trC P e z l
... | restrC Q u z′ | l′ = l′
Cf-trV (st-bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | Cf-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

Cf-tr⁻V (st-suc P) (Lv.s≈ e) z l with tr⁻C P e z | Cf-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻V (st-lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | Cf-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻V (st-fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | Cf-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
Cf-tr⁻V (st-bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | Cf-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

Cf-trL⁻ : ∀ {M A A′ π B φ χ} (d : Lk A A′) {x : O A′ π} {y : QQ B φ χ} → C M x y → C M (trL⁻ d x) y
Cf-trL⁻ (inj₁ e) r = Cf-tr⁻O e r
Cf-trL⁻ (inj₂ refl) r = r

Cf-trL : ∀ {M A A′ π B φ χ} (d : Lk A A′) {x : O A π} {y : QQ B φ χ} → C M x y → C M (trL d x) y
Cf-trL (inj₁ e) r = Cf-trO e r
Cf-trL (inj₂ refl) r = r
```
