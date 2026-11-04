# 闭包以下的树与累积树族 `Ordᶜ` 的互模拟 (判决: HOLDS, 只在闭包以下)

> 不含记号. 结论写在 [FeedGood](FeedGood.lagda.md). 由 [GuardTightCertRel](GuardTightCertRel.lagda.md) 用脚本生成: 对面的树从 `Ord` 上标 s 的版本换成 [GuardTightUni](GuardTightUni.lagda.md) 用的 `Ordᶜ` (原版多的 `ŝ`, `ĉᴸ` 这里用不到), 名字逐个替换, 证明逐字. `⌜_⌝`, `cb-sem`, `cu-sem`, `clash`, `Emp`, `lk≈` 等直接从原文件导入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGoodRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum
open Restr
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₀; rb-≈₀₀; em; em-≅)
open import OCF.Align.GuardTightCertRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; cb-sem; cu-sem; clash; Emp; out-intoU; out-intoC; out-intoV; cv-into; lk≈)
```

## §2 关系

```agda
module _ (B : Ordᴵ) (LR : ∀ {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordᶜ i → Set) where
  data R₊ : ∀ {A π} → O A π → Ordᶜ B → Set where
    rz  : ∀ {A π} → R₊ {A} {π} o0 zero
    rs  : ∀ {A π} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (os x) (suc ŷ)
    rl  : ∀ {A π} {F : ℕ → O A π} {f} → (∀ n → R₊ (F n) (f n)) → R₊ (ol F) (lim f)
    rwk : ∀ {A π ρ} {w : Wk π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (owk w x) ŷ
    rcv : ∀ {A π ρ} {w : Cov π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (ocv w x) ŷ
    rmk : ∀ {A π ξ k₁ k} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π}
            (r : k ◃₁ B) {ŷ′ : U k (◃₁→◃ r)} →
            LR (◃₁→◃ r) (outV R z) (out (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′) → R₊ (omk R lk ad z x) (up r ŷ′)
    rup : ∀ {A π k} {x : O A π} (r : k ◃₁ B) {ŷ′ : U k (◃₁→◃ r)} → LR (◃₁→◃ r) x (out (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′)
    rΩ  : ∀ {A π k j} (r : k < A) (cv : Adm (cov π) r) (q : j <ᴵ B) {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : U j (<→◃ q) → Ordᶜ B} →
          k ≈ ⌜ j ⌝ →
          (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordᶜ j) → LR (<→◃ q) z ẑ → R₊ (h ξ (intoU r z)) (f (into (<→◃ q) ẑ))) →
          R₊ (oΩ r cv h) (limᵢ q f)

Rs : ∀ B {A π} → O A π → Ordᶜ B → Set
LRs : ∀ B {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordᶜ i → Set
Rs B x y = R₊ B (LRs B) x y
LRs (suc k)   zero      x y = Rs k x y
LRs (suc c)   (suc r)   x y = LRs c r x y
LRs (lim f s) (self n)  x y = Rs (f n) x y
LRs (lim f s) (lim n r) x y = LRs (f n) r x y

outR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordᶜ k} → LRs c r z ẑ → Rs k z ẑ
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordᶜ k} → Rs k z ẑ → LRs c r z ẑ
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l

```

## §3 加法

```agda
R-⊕ : ∀ {A φ ψ k ℓ} {W : O A φ} {t : O A ψ} {Ŵ : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {t̂ : Ordᶜ k} → Rs ℓ W Ŵ → Rs k t t̂ → Rs ℓ (W ⊕ t) (add Ŵ σ t̂)
R-⊕ rW rz = rwk rW
R-⊕ rW (rs r) = rs (R-⊕ rW r)
R-⊕ rW (rl h) = rl (λ n → R-⊕ rW (h n))
R-⊕ rW (rwk r) = rwk (R-⊕ rW r)
R-⊕ rW (rcv r) = rcv (R-⊕ rW r)
R-⊕ rW (rmk zero l r) = R-⊕ rW r
R-⊕ rW (rmk (self n) l r) = R-⊕ rW r
R-⊕ rW (rup zero l) = R-⊕ rW l
R-⊕ rW (rup (self n) l) = R-⊕ rW l
R-⊕ {ℓ = ℓ} {Ŵ = Ŵ} {σ = σ} rW (rΩ r cv q {f = f} d h) =
  rΩ r _ (σ q) d (λ ξ em′ z ẑ l → rwk (subst (λ u → Rs ℓ (_ ⊕ _) (add Ŵ σ (f (into (<→◃ q) u))))
                                         (sym (out-into (<→◃ (σ q)) ẑ))
                                         (R-⊕ rW (h ξ em′ z ẑ (intoR (<→◃ q) (outR (<→◃ (σ q)) l))))))
```

## §4 搬运

左边 (`trO`, `tr⁻O`): 对 `≈` 与推导字典序递归. 右边 (`tr`, `tr⁻`): 对 `≅ᴵ` 与推导字典序递归.

```agda
BkOK : ∀ {k a b} {r : k < a} → RestrO r b → Set
BkOK w = ∀ {B ξ} {z : O (repO w) ξ} {ẑ : Ordᶜ B} → Rs B z ẑ → Rs B (backO w z) ẑ

R-trO  : ∀ {B A A′ π} (e : A ≈ A′) {x : O A π} {ŷ : Ordᶜ B} → Rs B x ŷ → Rs B (trO e x) ŷ
R-tr⁻O : ∀ {B A A′ π} (e : A ≈ A′) {x : O A′ π} {ŷ : Ordᶜ B} → Rs B x ŷ → Rs B (tr⁻O e x) ŷ
R-bk   : ∀ {k A A′} (q : k < A) (e : A ≈ A′) → BkOK (resO q e)
R-bk⁻  : ∀ {k A A′} (q : k < A′) (e : A ≈ A′) → BkOK (res⁻O q e)
R-trC  : ∀ {B k A A′ ξ} (P : Cp k A) (e : A ≈ A′) (z : Vc A P ξ) {ẑ : Ordᶜ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (trC P e z)) (valC (trC P e z))) ẑ
R-tr⁻C : ∀ {B k A A′ ξ} (P : Cp k A′) (e : A ≈ A′) (z : Vc A′ P ξ) {ẑ : Ordᶜ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (tr⁻C P e z)) (valC (tr⁻C P e z))) ẑ
R-trV  : ∀ {B k A A′ ξ} (R : Strict k A) (e : A ≈ A′) (z : Vs A R ξ) {ẑ : Ordᶜ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (trV R e z)) (valW (trV R e z))) ẑ
R-tr⁻V : ∀ {B k A A′ ξ} (R : Strict k A′) (e : A ≈ A′) (z : Vs A′ R ξ) {ẑ : Ordᶜ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (tr⁻V R e z)) (valW (tr⁻V R e z))) ẑ

R-trO e rz = rz
R-trO e (rs r) = rs (R-trO e r)
R-trO e (rl h) = rl (λ n → R-trO e (h n))
R-trO e (rwk r) = rwk (R-trO e r)
R-trO e (rcv r) = rcv (R-trO e r)
R-trO e (rmk {R = R} {z = z} zero l r) with trV R e z | R-trV R e z l
... | restrV R′ u z′ | l′ = rmk zero l′ (R-trO e r)
R-trO e (rmk {R = R} {z = z} (self n) l r) with trV R e z | R-trV R e z l
... | restrV R′ u z′ | l′ = rmk (self n) l′ (R-trO e r)
R-trO e (rup zero l) = rup zero (R-trO e l)
R-trO e (rup (self n) l) = rup (self n) (R-trO e l)
R-trO {B = B} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (resO r e)) _ q (≈-trans (≈-sym (eqO (resO r e))) d)
     (λ ξ em′ z ẑ l → R-trO e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (resO r e) u))) (f (into (<→◃ q) ẑ))) (sym (out-intoU (ltO (resO r e)) z))
                                     (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk r e (outR (<→◃ q) l))))))

R-tr⁻O e rz = rz
R-tr⁻O e (rs r) = rs (R-tr⁻O e r)
R-tr⁻O e (rl h) = rl (λ n → R-tr⁻O e (h n))
R-tr⁻O e (rwk r) = rwk (R-tr⁻O e r)
R-tr⁻O e (rcv r) = rcv (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} zero l r) with tr⁻V R e z | R-tr⁻V R e z l
... | restrV R′ u z′ | l′ = rmk zero l′ (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} (self n) l r) with tr⁻V R e z | R-tr⁻V R e z l
... | restrV R′ u z′ | l′ = rmk (self n) l′ (R-tr⁻O e r)
R-tr⁻O e (rup zero l) = rup zero (R-tr⁻O e l)
R-tr⁻O e (rup (self n) l) = rup (self n) (R-tr⁻O e l)
R-tr⁻O {B = B} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (res⁻O r e)) _ q (≈-trans (≈-sym (eqO (res⁻O r e))) d)
     (λ ξ em′ z ẑ l → R-tr⁻O e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f (into (<→◃ q) ẑ))) (sym (out-intoU (ltO (res⁻O r e)) z))
                                      (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk⁻ r e (outR (<→◃ q) l))))))

R-bk Lv.zero (Lv.s≈ e) = R-tr⁻O e
R-bk (Lv.suc r) (Lv.s≈ e) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.lim n r) (Lv.l≈ h) with resO r (h n) | R-bk r (h n)
... | restrO d m t b | H = H
R-bk (Lv.fst r) (Lv.o≈ d′ e h) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with resO r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η)) | R-bk r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-bk⁻ Lv.zero (Lv.s≈ e) = R-trO e
R-bk⁻ (Lv.suc r) (Lv.s≈ e) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.lim n r) (Lv.l≈ h) with res⁻O r (h n) | R-bk⁻ r (h n)
... | restrO d m t b | H = H
R-bk⁻ (Lv.fst r) (Lv.o≈ d′ e h) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with res⁻O r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η)) | R-bk⁻ r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-trC Lv.self e z l = R-trO e l
R-trC (Lv.suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻C Lv.self e z l = R-tr⁻O e l
R-tr⁻C (Lv.suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trV (st-suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trV (st-fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻V (st-suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trL⁻ : ∀ {B A A′ π} (d : Lk A A′) {x : O A′ π} {ŷ : Ordᶜ B} → Rs B x ŷ → Rs B (trL⁻ d x) ŷ
R-trL⁻ (inj₁ e) r = R-tr⁻O e r
R-trL⁻ (inj₂ refl) r = r

R-trL : ∀ {B A A′ π} (d : Lk A A′) {x : O A π} {ŷ : Ordᶜ B} → Rs B x ŷ → Rs B (trL d x) ŷ
R-trL (inj₁ e) r = R-trO e r
R-trL (inj₂ refl) r = r
```

**右边.** `Ordᶜ` 上的搬运.

```agda
R-tr  : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordᶜ a} → Rs a x ŷ → Rs b x (tr e ŷ)
R-tr⁻ : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordᶜ b} → Rs b x ŷ → Rs a x (tr⁻ e ŷ)
R-bkˢ  : ∀ {j a b A ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordᶜ (rep (res q e))} → Rs (rep (res q e)) z ẑ → Rs j z (back (res q e) ẑ)
R-bk⁻ˢ : ∀ {j a b A ξ} (q : j <ᴵ b) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordᶜ (rep (res⁻ q e))} → Rs (rep (res⁻ q e)) z ẑ → Rs j z (back (res⁻ q e) ẑ)

R-tr e rz = rz
R-tr e (rs r) = rs (R-tr e r)
R-tr e (rl h) = rl (λ n → R-tr e (h n))
R-tr e (rwk r) = rwk (R-tr e r)
R-tr e (rcv r) = rcv (R-tr e r)
R-tr (s≅ e) (rmk zero l r) = rmk zero (R-tr e l) (R-tr (s≅ e) r)
R-tr (l≅ h) (rmk (self n) l r) = rmk (self n) (R-tr (h n) l) (R-tr (l≅ h) r)
R-tr (s≅ e) (rup zero l) = rup zero (R-tr e l)
R-tr (l≅ h) (rup (self n) l) = rup (self n) (R-tr (h n) l)
R-tr {b = b} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (lt (res q e)) (≈-trans d (⌜≈⌝ (eq (res q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs b (h₁ ξ (intoU r z)) (tr e (f (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) ẑ))
                             (R-tr e (h ξ em′ z _ (intoR (<→◃ q) (R-bkˢ q e (outR (<→◃ (lt (res q e))) l))))))

R-tr⁻ e rz = rz
R-tr⁻ e (rs r) = rs (R-tr⁻ e r)
R-tr⁻ e (rl h) = rl (λ n → R-tr⁻ e (h n))
R-tr⁻ e (rwk r) = rwk (R-tr⁻ e r)
R-tr⁻ e (rcv r) = rcv (R-tr⁻ e r)
R-tr⁻ (s≅ e) (rmk zero l r) = rmk zero (R-tr⁻ e l) (R-tr⁻ (s≅ e) r)
R-tr⁻ (l≅ h) (rmk (self n) l r) = rmk (self n) (R-tr⁻ (h n) l) (R-tr⁻ (l≅ h) r)
R-tr⁻ (s≅ e) (rup zero l) = rup zero (R-tr⁻ e l)
R-tr⁻ (l≅ h) (rup (self n) l) = rup (self n) (R-tr⁻ (h n) l)
R-tr⁻ {a = a} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (lt (res⁻ q e)) (≈-trans d (⌜≈⌝ (eq (res⁻ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs a (h₁ ξ (intoU r z)) (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) ẑ))
                             (R-tr⁻ e (h ξ em′ z _ (intoR (<→◃ q) (R-bk⁻ˢ q e (outR (<→◃ (lt (res⁻ q e))) l))))))

R-bkˢ zero (s≅ e) l = R-tr⁻ e l
R-bkˢ (suc q) (s≅ e) l = R-bkˢ q e l
R-bkˢ (lim n q) (l≅ h) l = R-bkˢ q (h n) l

R-bk⁻ˢ zero (s≅ e) l = R-tr e l
R-bk⁻ˢ (suc q) (s≅ e) l = R-bk⁻ˢ q e l
R-bk⁻ˢ (lim n q) (l≅ h) l = R-bk⁻ˢ q (h n) l
```

## §5 嵌入, $\dot\Omega$

`R-ι`: 嵌入不改对面的树. `omk` 的一行: 输入的 $z$ 与对面的 $\hat y'$ 有关系, 输出的 $x$ 是 $z$ 嵌到规范位置, 所以记号的两半都还在.

```agda
BLOK : ∀ {k a b} {r : k < a} → RL r b → Set
BLOK w = ∀ {B ξ} {z : O (repL w) ξ} {ẑ : Ordᶜ B} → Rs B z ẑ → Rs B (backL w z) ẑ

R-bL : ∀ {k a b} (r : k < a) (d : Lk a b) → BLOK (resL r d)
R-bL r (inj₁ e) with resO r e | R-bk r e
... | restrO d′ l t b | H = H
R-bL r (inj₂ refl) = λ l → l

module EmbRᶜ (L : LG) (tc : Tc L) where
  open Emb L tc

  ιC-eq : ∀ a {k ξ a′} (Q : Cp k a) (P : Cp a′ L) (d : Lk k a′) (z : Vc a Q ξ) → ιC a Q P d z ≡ ι k P d (outC Q z)
  ιC-eq a Lv.self P d z = refl
  ιC-eq (Lv.suc b) (Lv.suc Q) P d z = ιC-eq b Q P d z
  ιC-eq (Lv.lim f) (Lv.lim n Q) P d z = ιC-eq (f n) Q P d z
  ιC-eq (Lv.lc c t g) (Lv.fst Q) P d z = ιC-eq t Q P d z
  ιC-eq (Lv.lc c t g) (Lv.bra η e Q) P d z = ιC-eq (g η e) Q P d z

  ιV-eq : ∀ a {k ξ a′} (R : Strict k a) (P : Cp a′ L) (d : Lk k a′) (z : Vs a R ξ) → ιV a R P d z ≡ ι k P d (outV R z)
  ιV-eq (Lv.suc b) (st-suc Q) P d z = ιC-eq b Q P d z
  ιV-eq (Lv.lim f) (st-lim n Q) P d z = ιC-eq (f n) Q P d z
  ιV-eq (Lv.lc c t g) (st-fst Q) P d z = ιC-eq t Q P d z
  ιV-eq (Lv.lc c t g) (st-bra η e Q) P d z = ιC-eq (g η e) Q P d z

  R-ι : ∀ {B a a′ π} (P : Cp a′ L) (d : Lk a a′) {z : O a π} {ŷ : Ordᶜ B} → Rs B z ŷ → Rs B (ι a P d z) ŷ
  R-ι P d rz = rz
  R-ι P d (rs r) = rs (R-ι P d r)
  R-ι P d (rl h) = rl (λ n → R-ι P d (h n))
  R-ι P d (rwk r) = rwk (R-ι P d r)
  R-ι P d (rcv r) = rcv (R-ι P d r)
  R-ι P d (rup zero l) = rup zero (R-ι P d l)
  R-ι P d (rup (self n) l) = rup (self n) (R-ι P d l)
  R-ι {a = a} P d (rmk {R = R} {z = z} zero l r) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r′ =
    rcv (rmk zero (subst (λ w → Rs _ w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             (rup zero (subst (λ w → Rs _ w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) l))))
  R-ι {a = a} P d (rmk {R = R} {z = z} (self n) l r) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r′ =
    rcv (rmk (self n) (subst (λ w → Rs _ w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             (rup (self n) (subst (λ w → Rs _ w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) l))))
  R-ι {B = B} {a = a} P d (rΩ {j = j} r cv q {h = h₁} {f = f} dk h) with resL r d | R-bL r d
  ... | rl e′ s u b | H =
    rΩ (P ◁ s) _ q (lk≈ e′ dk)
       (λ ξ em′ z ẑ l → rwk (R-ι P d (subst (λ w → Rs B (h₁ ξ (intoU r (b w))) (f (into (<→◃ q) ẑ))) (sym (cv-into P s z))
                                             (h ξ em′ (b z) ẑ (intoR (<→◃ q) (H (outR (<→◃ q) l)))))))

RΩ̇ : ∀ i {t} → t ≈ ⌜ i ⌝ → (tc : Tc t) → Rs i (Ω̇ t tc) (Ω i)
RΩ̇ zero Lv.z≈ tc = rs rz
RΩ̇ (suc b) {t = Lv.suc t′} (Lv.s≈ e) tc =
  rΩ Lv.zero tt zero e (λ ξ em′ z ẑ l → rmk zero l (rup zero (EmbRᶜ.R-ι (Lv.suc t′) tc (Lv.suc Lv.self) (inj₂ refl) l)))
RΩ̇ (lim g s) {t = Lv.lim f′} (Lv.l≈ h) tc =
  rl (λ n → rwk (rmk (self n) (RΩ̇ (g n) (h n) (tc n)) (rup (self n) (EmbRᶜ.R-ι (Lv.lim f′) tc (Lv.lim n Lv.self) (inj₂ refl) (RΩ̇ (g n) (h n) (tc n))))))
```
