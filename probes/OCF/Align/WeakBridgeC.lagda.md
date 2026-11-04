# 不带高度的树接上带高度的树 (二′: 关系 `C`)

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 分文件只为编译的内存.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeC where

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
open I using (q0; qs; ql; qi; qŝ; qĉ; qclo; qwk; qΩ) renaming (omk to qmk; _⊞_ to _⊞_)
```


## §4 关系

`Rs` 是 [GuardCertRel](GuardCertRel.lagda.md) 的, 对低层. `cml` 的第一个参数是整条 `rmk`.

```agda
module CR where
  open import OCF.Align.GuardCertRel public using (Rs; Md; fr; gd; rmk; rz; rs; rl; rwk; rcv; rΩ; rŝ; rĉ; rĉŝ; Rz; outR; intoR; LRs; R-trO; R-tr⁻O; R-bk; R-bk⁻; R-trV; R-tr⁻V; trV-≈; tr⁻V-≈; iv-trV; iv-tr⁻V; R-trL; R-trL⁻; lk≈′; IvOf; mdOf; InvS; HPf; module EmbR; Hr; RΩ̇; FlrLe)
open CR using (Rs; Md; fr; gd; Hr; HPf; rmk)

cvOf : ∀ {π k₀ φ} → CR.FlrLe π k₀ → (∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) → CvL π φ
cvOf c cv f m e = ⊑ᴵ-trans (c f m) (Sim→⊑ᴵ (cv e))

module _ (M : Ordᴵ) (LR : ∀ {i} → i ◃ M → ∀ {A ξ j φ χ} → O A ξ → QQ j φ χ → Set) where
  data C₊ : ∀ {A π B φ χ} → O A π → QQ B φ χ → Set where
    cz  : ∀ {A π B φ χ} → C₊ {A} {π} {B} {φ} {χ} o0 q0
    cs  : ∀ {A π B φ χ} {x : O A π} {y : QQ B φ χ} → CvL π φ → C₊ x y → C₊ (os x) (qs y)
    cl  : ∀ {A π B φ χ} {F : ℕ → O A π} {H : ℕ → QQ B φ χ} → (∀ n → C₊ (F n) (H n)) → C₊ (ol F) (ql H)
    cwl : ∀ {A π ρ B φ χ} {w : Wk π ρ} {x : O A π} {y : QQ B φ χ} → C₊ x y → C₊ (owk w x) y
    cvl : ∀ {A π ρ B φ χ} {w : Cov π ρ} {x : O A π} {y : QQ B φ χ} → C₊ x y → C₊ (ocv w x) y
    cwr : ∀ {A π B φ ψ χ χ′} {le : ∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ} {le′ : I.Sub 0 χ′ χ} {x : O A π} {y : QQ B φ χ} → C₊ x y → C₊ x (qwk le le′ y)
    cdr : ∀ {A π B φ χ k} {r : k ◃₁ B} {z : I.Us 0 k (◃₁→◃ r) φ χ} {x : O A π} {y : QQ B φ χ} → C₊ x y → C₊ x (qmk r z y)
    cm  : ∀ {A π ξ k₁ B φ χ i j φ̂ χ̂} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π} {y : QQ B φ χ} {ẑ : QQ j φ̂ χ̂}
            (r : i ◃ M) (l : Ops j B) → k₁ ≈ c⁺ j → LR r (outV R z) ẑ → ap l ẑ ≃ y → C₊ x y → C₊ (omk R lk ad z x) y
    cml : ∀ {A π ξ k₁ B φ χ k₀ k₀′ c′ φ̂ χ̂ m₀} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π} {y : QQ B φ χ}
            (r : k₀′ ◃₁ k₀) {ŷ′ : Uˢ k₀′ (◃₁→◃ r)} (cv : ∀ {ℓ} → Ev ℓ φ̂ → Simᴵ k₀ ℓ) (l : Ops c′ B) →
            Rs k₀ m₀ (omk R lk ad z x) (Ord₊ˢ.up r ŷ′) → ap l (I.tl {m = 0} {c = c′} {χ = χ̂} φ̂ cv (Ord₊ˢ.up r ŷ′)) ≃ y → C₊ x y → C₊ (omk R lk ad z x) y
    ci  : ∀ {A π B φ χ k j} (r : k < A) {cv : Adm (cov π) r} {ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ} {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : Ordˢ j → QQ B φ χ} →
          k ≈ ⌜ j ⌝ → (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → Rs j fr z ẑ → C₊ (h ξ (intoU r z)) (f ẑ)) → C₊ (oΩ r cv h) (qi ac f)
    cΩ  : ∀ {A π B φ χ k j j₂} (r : k < A) {cv : Adm (cov π) r} {fe : ∀ {ℓ} → Ev ℓ φ → Ev ℓ FT.Fl} (q : j <ᴵ B)
            {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : ∀ ξ ζ → I.Us 0 j (<→◃ q) ξ ζ → QQ B (ξ ⊔ φ) (I.lo 0 ζ I.∪ χ)} →
          k ≈ c⁺ j → j ≅ᴵ j₂ → (q₂ : j₂ <ᴵ M) → CvL π φ →
          (∀ ξ ξ̂ ζ → CvL ξ ξ̂ → (z : O k ξ) (ẑ : QQ j ξ̂ ζ) → LR (<→◃ q₂) z ẑ → C₊ (h ξ (intoU r z)) (f ξ̂ ζ (I.intoU (<→◃ q) ẑ))) →
          C₊ (oΩ r cv h) (qΩ fe q f)
    cŝ  : ∀ {A π B φ χ c₀ c′} {t : O A π} {g : ∀ η → c₀ ⊑ᴵ η → O A π} {t̂ : QQ B φ χ} {ĝ : ∀ η → c′ ⊑ᴵ η → QQ B φ χ} →
          Nz A → c₀ ⊑ᴵ c′ → C₊ t t̂ → (∀ η e e′ → C₊ (g η e) (ĝ η e′)) → C₊ (oŝ c₀ t g) (qŝ c′ t̂ ĝ)
    cĉ  : ∀ {A π B φ χ c₀ c′ z ẑ} {zg : ∀ η → c₀ ⊑ᴵ η → Z} {ẑg : ∀ η → c′ ⊑ᴵ η → Z} {o₀ : O A π} {o : ∀ η → c₀ ⊑ᴵ η → O A π} {ô₀ : QQ B φ χ} {ô : ∀ η → c′ ⊑ᴵ η → QQ B φ χ} →
          c₀ ⊑ᴵ c′ → z ≲ᶻ ẑ → (∀ η e e′ → zg η e ≲ᶻ ẑg η e′) → C₊ o₀ ô₀ → (∀ η e e′ → C₊ (o η e) (ô η e′)) → C₊ (oĉ c₀ z zg o₀ o) (qĉ c′ ẑ ẑg ô₀ ô)
    ccl : ∀ {A π B φ χ c₁′ t₁′ g₁′ c₂ t₂ g₂} {P : Cp (lc c₂ t₂ g₂) A} {k : Lk (lc c₂ t₂ g₂) (lc c₁′ t₁′ g₁′)} {ad : AdmC (cov π) P}
            {t : O A π} {g : ∀ η e → O A (π ∪ tk (frm c₁′ t₁′ g₁′ η e))} {t̂ : QQ B (φ ⊔ fk zero) χ} {ĝ : ∀ η → QQ B (φ ⊔ fk η) χ} →
          CvL π φ → C₊ t t̂ → (∀ η e → C₊ (g η e) (ĝ η)) → C₊ (ocl P k ad t g) (qclo t̂ ĝ)

C : Ordᴵ → ∀ {A π B φ χ} → O A π → QQ B φ χ → Set
LC : ∀ M {i} → i ◃ M → ∀ {A ξ j φ χ} → O A ξ → QQ j φ χ → Set
C M x y = C₊ M (LC M) x y
LC (suc k)   zero      x y = C k x y
LC (suc c)   (suc r)   x y = LC c r x y
LC (lim f s) (self n)  x y = C (f n) x y
LC (lim f s) (lim n r) x y = LC (f n) r x y

outL : ∀ {c k} (r : k ◃ c) {A ξ j φ χ} {z : O A ξ} {ẑ : QQ j φ χ} → LC c r z ẑ → C k z ẑ
outL zero      l = l
outL (suc r)   l = outL r l
outL (self n)  l = l
outL (lim n r) l = outL r l

intoL : ∀ {c k} (r : k ◃ c) {A ξ j φ χ} {z : O A ξ} {ẑ : QQ j φ χ} → C k z ẑ → LC c r z ẑ
intoL zero      l = l
intoL (suc r)   l = intoL r l
intoL (self n)  l = l
intoL (lim n r) l = intoL r l

outU-into : ∀ {k B} (r : k ◃ B) {ξ ζ} (x : QQ k ξ ζ) → I.outU r (I.intoU r x) ≡ x
outU-into zero x = refl
outU-into (suc r) x = outU-into r x
outU-into (self n) x = refl
outU-into (lim n r) x = outU-into r x
```

## §5 界变大

`C-up`: `M` 只限制节点. 负出现经 `outL`, `intoL` 都到 `C j₂`, 所以两边同一个.

```agda
◃-trans : ∀ {i a b} → i ◃ a → a ◃ b → i ◃ b
◃-trans r zero = suc r
◃-trans r (suc s) = suc (◃-trans r s)
◃-trans r (self n) = lim n r
◃-trans r (lim n s) = lim n (◃-trans r s)

C-up : ∀ {i M} (s : i ◃ M) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → C i x y → C M x y
C-up s cz = cz
C-up s (cs c D) = cs c (C-up s D)
C-up s (cl h) = cl (λ n → C-up s (h n))
C-up s (cwl D) = cwl (C-up s D)
C-up s (cvl D) = cvl (C-up s D)
C-up s (cwr D) = cwr (C-up s D)
C-up s (cdr D) = cdr (C-up s D)
C-up s (cm r l dk lr E D) = cm (◃-trans r s) l dk (intoL (◃-trans r s) (outL r lr)) E (C-up s D)
C-up s (cml r cv l d E D) = cml r cv l d E (C-up s D)
C-up s (ci r dk prem) = ci r dk (λ ξ em z ẑ l → C-up s (prem ξ em z ẑ l))
C-up s (cΩ r q dk e₂ q₂ c prem) = cΩ r q dk e₂ (FT.<◃ q₂ s) c (λ ξ ξ̂ ζ cv z ẑ l → C-up s (prem ξ ξ̂ ζ cv z ẑ (intoL (<→◃ q₂) (outL (<→◃ (FT.<◃ q₂ s)) l))))
C-up s (cŝ n ec rt rg) = cŝ n ec (C-up s rt) (λ η e e′ → C-up s (rg η e e′))
C-up s (cĉ ec dz dg ro rg) = cĉ ec dz dg (C-up s ro) (λ η e e′ → C-up s (rg η e e′))
C-up s (ccl c rt rg) = ccl c (C-up s rt) (λ η e → C-up s (rg η e))
```

**界沿 `≅` 搬运.** 递归同 `R-trˢ`: 对 `≅` 与推导字典序.

```agda
rep◃ : ∀ {i a b} → i ◃ a → a ≅ᴵ b → Ordᴵ
pos◃ : ∀ {i a b} (r : i ◃ a) (d : a ≅ᴵ b) → rep◃ r d ◃ b
rep◃ {i = i} zero (s≅ {b = b} e) = b
rep◃ (suc r) (s≅ e) = rep◃ r e
rep◃ (self {f = f} n) (l≅ {g = g} h) = g n
rep◃ (lim n r) (l≅ h) = rep◃ r (h n)
pos◃ zero (s≅ e) = zero
pos◃ (suc r) (s≅ e) = suc (pos◃ r e)
pos◃ (self n) (l≅ h) = self n
pos◃ (lim n r) (l≅ h) = lim n (pos◃ r (h n))

rep< : ∀ {i a b} → i <ᴵ a → a ≅ᴵ b → Ordᴵ
pos< : ∀ {i a b} (r : i <ᴵ a) (d : a ≅ᴵ b) → rep< r d <ᴵ b
rep≅ : ∀ {i a b} (r : i <ᴵ a) (d : a ≅ᴵ b) → i ≅ᴵ rep< r d
rep< zero (s≅ {b = b} e) = b
rep< (suc r) (s≅ e) = rep< r e
rep< (lim n r) (l≅ h) = rep< r (h n)
pos< zero (s≅ e) = zero
pos< (suc r) (s≅ e) = suc (pos< r e)
pos< (lim n r) (l≅ h) = lim n (pos< r (h n))
rep≅ zero (s≅ e) = e
rep≅ (suc r) (s≅ e) = rep≅ r e
rep≅ (lim n r) (l≅ h) = rep≅ r (h n)

C-≅  : ∀ {a b} (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → C a x y → C b x y
C-≅⁻ : ∀ {a b} (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → C b x y → C a x y
Lmv  : ∀ {i a b} (r : i ◃ a) (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → LC a r x y → LC b (pos◃ r d) x y
Lmv⁻ : ∀ {i a b} (r : i <ᴵ a) (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → LC b (<→◃ (pos< r d)) x y → LC a (<→◃ r) x y
Lmv₂ : ∀ {i a b} (r : i ◃ b) (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → LC b r x y → LC a (pos◃ r (≅ᴵ-sym d)) x y
Lmv₂⁻ : ∀ {i a b} (r : i <ᴵ b) (d : a ≅ᴵ b) {A π B φ χ} {x : O A π} {y : QQ B φ χ} → LC a (<→◃ (pos< r (≅ᴵ-sym d))) x y → LC b (<→◃ r) x y

Lmv zero (s≅ e) l = C-≅ e l
Lmv (suc r) (s≅ e) l = Lmv r e l
Lmv (self n) (l≅ h) l = C-≅ (h n) l
Lmv (lim n r) (l≅ h) l = Lmv r (h n) l

Lmv⁻ zero (s≅ e) l = C-≅⁻ e l
Lmv⁻ (suc r) (s≅ e) l = Lmv⁻ r e l
Lmv⁻ (lim n r) (l≅ h) l = Lmv⁻ r (h n) l

Lmv₂ zero (s≅ e) l = C-≅⁻ e l
Lmv₂ (suc r) (s≅ e) l = Lmv₂ r e l
Lmv₂ (self n) (l≅ h) l = C-≅⁻ (h n) l
Lmv₂ (lim n r) (l≅ h) l = Lmv₂ r (h n) l

Lmv₂⁻ zero (s≅ e) l = C-≅ e l
Lmv₂⁻ (suc r) (s≅ e) l = Lmv₂⁻ r e l
Lmv₂⁻ (lim n r) (l≅ h) l = Lmv₂⁻ r (h n) l

C-≅ d cz = cz
C-≅ d (cs c D) = cs c (C-≅ d D)
C-≅ d (cl h) = cl (λ n → C-≅ d (h n))
C-≅ d (cwl D) = cwl (C-≅ d D)
C-≅ d (cvl D) = cvl (C-≅ d D)
C-≅ d (cwr D) = cwr (C-≅ d D)
C-≅ d (cdr D) = cdr (C-≅ d D)
C-≅ d (cm r l dk lr E D) = cm (pos◃ r d) l dk (Lmv r d lr) E (C-≅ d D)
C-≅ d (cml r cv l p E D) = cml r cv l p E (C-≅ d D)
C-≅ d (ci r dk prem) = ci r dk (λ ξ em z ẑ l → C-≅ d (prem ξ em z ẑ l))
C-≅ d (cΩ r q dk e₂ q₂ c prem) = cΩ r q dk (≅ᴵ-trans e₂ (rep≅ q₂ d)) (pos< q₂ d) c (λ ξ ξ̂ ζ cv z ẑ l → C-≅ d (prem ξ ξ̂ ζ cv z ẑ (Lmv⁻ q₂ d l)))
C-≅ d (cŝ n ec rt rg) = cŝ n ec (C-≅ d rt) (λ η e e′ → C-≅ d (rg η e e′))
C-≅ d (cĉ ec dz dg ro rg) = cĉ ec dz dg (C-≅ d ro) (λ η e e′ → C-≅ d (rg η e e′))
C-≅ d (ccl c rt rg) = ccl c (C-≅ d rt) (λ η e → C-≅ d (rg η e))

C-≅⁻ d cz = cz
C-≅⁻ d (cs c D) = cs c (C-≅⁻ d D)
C-≅⁻ d (cl h) = cl (λ n → C-≅⁻ d (h n))
C-≅⁻ d (cwl D) = cwl (C-≅⁻ d D)
C-≅⁻ d (cvl D) = cvl (C-≅⁻ d D)
C-≅⁻ d (cwr D) = cwr (C-≅⁻ d D)
C-≅⁻ d (cdr D) = cdr (C-≅⁻ d D)
C-≅⁻ d (cm r l dk lr E D) = cm (pos◃ r (≅ᴵ-sym d)) l dk (Lmv₂ r d lr) E (C-≅⁻ d D)
C-≅⁻ d (cml r cv l p E D) = cml r cv l p E (C-≅⁻ d D)
C-≅⁻ d (ci r dk prem) = ci r dk (λ ξ em z ẑ l → C-≅⁻ d (prem ξ em z ẑ l))
C-≅⁻ d (cΩ r q dk e₂ q₂ c prem) = cΩ r q dk (≅ᴵ-trans e₂ (rep≅ q₂ (≅ᴵ-sym d))) (pos< q₂ (≅ᴵ-sym d)) c (λ ξ ξ̂ ζ cv z ẑ l → C-≅⁻ d (prem ξ ξ̂ ζ cv z ẑ (Lmv₂⁻ q₂ d l)))
C-≅⁻ d (cŝ n ec rt rg) = cŝ n ec (C-≅⁻ d rt) (λ η e e′ → C-≅⁻ d (rg η e e′))
C-≅⁻ d (cĉ ec dz dg ro rg) = cĉ ec dz dg (C-≅⁻ d ro) (λ η e e′ → C-≅⁻ d (rg η e e′))
C-≅⁻ d (ccl c rt rg) = ccl c (C-≅⁻ d rt) (λ η e → C-≅⁻ d (rg η e))
```
