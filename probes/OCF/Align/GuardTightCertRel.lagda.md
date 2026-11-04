# 证书 (一): 闭包以下的树与 `Ordˢ` 的互模拟

> 不含记号. 结论写在 [GuardTight](GuardTight.lagda.md). `Rs B x ŷ`: 任何层 $A$ 上没有闭包的值 $x$ 与 `Ordˢ B` 的树 $\hat y$ 同形. 节点的层 $k$ 模 `≈` 就是 $\lceil j\rceil$ ($j$ 是对面节点的层). 与 [UniformNF5Base](UniformNF5Base.lagda.md) 的 `R₊` 同形. **`rmk` 同时记 $z$ 与 $x$: `ι` 读 $z$, 其余读 $x$.** 节点的地板 $\xi$ 只取空的 (`Emp`): 闭包以下的层里没有闭包, 链的地板总是空的 (`trim-emp`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightCertRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum
open import OCF.Free.Prefix using (Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; coeˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Restrˢ; Ωˢ)
open Ord₊ˢ
open Restrˢ
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₀; rb-≈₀₀; em; em-≅)
```

## §1 $\lceil a\rceil$

```agda
⌜_⌝ : Ordᴵ → LG
⌜ a ⌝ = rb₀ (em a)

⌜≈⌝ : ∀ {a b} → a ≅ᴵ b → ⌜ a ⌝ ≈ ⌜ b ⌝
⌜≈⌝ e = rb-≈₀₀ (em-≅ e)

⌜≈⁻⌝ : ∀ {a b} → ⌜ a ⌝ ≈ ⌜ b ⌝ → a ≅ᴵ b
⌜≈⁻⌝ {a = zero} {b = zero} Lv.z≈ = z≅
⌜≈⁻⌝ {a = suc a} {b = suc b} (Lv.s≈ e) = s≅ (⌜≈⁻⌝ e)
⌜≈⁻⌝ {a = lim f s} {b = lim g t} (Lv.l≈ h) = l≅ (λ n → ⌜≈⁻⌝ (h n))

pullG : ∀ a {k} → k < ⌜ a ⌝ → Σ Ordᴵ λ a′ → (k ≡ ⌜ a′ ⌝) × (a′ <ᴵ a)
pullG (suc a) Lv.zero = a , refl , zero
pullG (suc a) (Lv.suc r) with pullG a r
... | a′ , e , q = a′ , e , suc q
pullG (lim f s) (Lv.lim n r) with pullG (f n) r
... | a′ , e , q = a′ , e , lim n q

data FrL : LG → Set where
  fz : FrL Lv.zero
  fs′ : ∀ {b} → FrL b → FrL (Lv.suc b)
  fl : ∀ {f} → (∀ n → FrL (f n)) → FrL (Lv.lim f)

FrG : ∀ a → FrL ⌜ a ⌝
FrG zero = fz
FrG (suc a) = fs′ (FrG a)
FrG (lim f s) = fl (λ n → FrG (f n))

Fr≈ : ∀ {a b} → FrL a → a ≈ b → FrL b
Fr≈ fz Lv.z≈ = fz
Fr≈ (fs′ h) (Lv.s≈ e) = fs′ (Fr≈ h e)
Fr≈ (fl h) (Lv.l≈ e) = fl (λ n → Fr≈ (h n) (e n))

-- 比较的语义
cb-sem : ∀ {t k rp i j} → t ≈ ⌜ i ⌝ → k ≈ ⌜ j ⌝ → k ≈ rp → rp < t → j ≺ᴵ i
cb-sem {i = i} et ek d s with ≈-move et s
... | viaᴸ d′ s′ _ with pullG i s′
... | a′ , refl , q = via (⌜≈⁻⌝ (≈-trans (≈-sym ek) (≈-trans d d′))) q

cu-sem : ∀ {t k i j} → t ≈ ⌜ i ⌝ → k ≈ ⌜ j ⌝ → (t ≈ k ⊎ Below t k) → (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
cu-sem et ek (inj₁ d) = inj₂ (⌜≈⁻⌝ (≈-trans (≈-sym et) (≈-trans d ek)))
cu-sem {j = j} et ek (inj₂ (pre d s)) with ≈-move ek s
... | viaᴸ d′ s′ _ with pullG j s′
... | a′ , refl , q = inj₁ (via (⌜≈⁻⌝ (≈-trans (≈-sym et) (≈-trans d d′))) q)

clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)
```

## §2 关系

```agda
Emp : Fl → Set
Emp ξ = ∀ {f} → Mem ξ f → ⊥

module _ (B : Ordᴵ) (LR : ∀ {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set) where
  data R₊ : ∀ {A π} → O A π → Ordˢ B → Set where
    rz  : ∀ {A π} → R₊ {A} {π} o0 zero
    rs  : ∀ {A π} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (os x) (suc ŷ)
    rl  : ∀ {A π} {F : ℕ → O A π} {f} → (∀ n → R₊ (F n) (f n)) → R₊ (ol F) (lim f)
    rwk : ∀ {A π ρ} {w : Wk π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (owk w x) ŷ
    rcv : ∀ {A π ρ} {w : Cov π ρ} {x : O A π} {ŷ} → R₊ x ŷ → R₊ (ocv w x) ŷ
    rmk : ∀ {A π ξ k₁ k} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π}
            (r : k ◃₁ B) {ŷ′ : Uˢ k (◃₁→◃ r)} →
            LR (◃₁→◃ r) (outV R z) (outˢ (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′) → R₊ (omk R lk ad z x) (up r ŷ′)
    rup : ∀ {A π k} {x : O A π} (r : k ◃₁ B) {ŷ′ : Uˢ k (◃₁→◃ r)} → LR (◃₁→◃ r) x (outˢ (◃₁→◃ r) ŷ′) → R₊ x (up r ŷ′)
    rΩ  : ∀ {A π k j} (r : k < A) (cv : Adm (cov π) r) (q : j <ᴵ B) {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : Uˢ j (<→◃ q) → Ordˢ B} →
          k ≈ ⌜ j ⌝ →
          (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → LR (<→◃ q) z ẑ → R₊ (h ξ (intoU r z)) (f (intoˢ (<→◃ q) ẑ))) →
          R₊ (oΩ r cv h) (limᵢ q f)

Rs : ∀ B {A π} → O A π → Ordˢ B → Set
LRs : ∀ B {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set
Rs B x y = R₊ B (LRs B) x y
LRs (suc k)   zero      x y = Rs k x y
LRs (suc c)   (suc r)   x y = LRs c r x y
LRs (lim f s) (self n)  x y = Rs (f n) x y
LRs (lim f s) (lim n r) x y = LRs (f n) r x y

outR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → LRs c r z ẑ → Rs k z ẑ
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {c k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → Rs k z ẑ → LRs c r z ẑ
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l

out-intoU : ∀ {L k} (r : k < L) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU Lv.zero        z = refl
out-intoU (Lv.suc r)     z = out-intoU r z
out-intoU (Lv.lim n r)   z = out-intoU r z
out-intoU (Lv.fst r)     z = out-intoU r z
out-intoU (Lv.bra η e r) z = out-intoU r z
```

## §3 加法

```agda
R-⊕ : ∀ {A φ ψ k ℓ} {W : O A φ} {t : O A ψ} {Ŵ : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t̂ : Ordˢ k} → Rs ℓ W Ŵ → Rs k t t̂ → Rs ℓ (W ⊕ t) (addˢ Ŵ σ t̂)
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
  rΩ r _ (σ q) d (λ ξ em′ z ẑ l → rwk (subst (λ u → Rs ℓ (_ ⊕ _) (addˢ Ŵ σ (f (intoˢ (<→◃ q) u))))
                                         (sym (out-intoˢ (<→◃ (σ q)) ẑ))
                                         (R-⊕ rW (h ξ em′ z ẑ (intoR (<→◃ q) (outR (<→◃ (σ q)) l))))))
```

## §4 搬运

左边 (`trO`, `tr⁻O`): 对 `≈` 与推导字典序递归. 右边 (`trˢ`, `tr⁻ˢ`): 对 `≅ᴵ` 与推导字典序递归.

```agda
BkOK : ∀ {k a b} {r : k < a} → RestrO r b → Set
BkOK w = ∀ {B ξ} {z : O (repO w) ξ} {ẑ : Ordˢ B} → Rs B z ẑ → Rs B (backO w z) ẑ

R-trO  : ∀ {B A A′ π} (e : A ≈ A′) {x : O A π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trO e x) ŷ
R-tr⁻O : ∀ {B A A′ π} (e : A ≈ A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (tr⁻O e x) ŷ
R-bk   : ∀ {k A A′} (q : k < A) (e : A ≈ A′) → BkOK (resO q e)
R-bk⁻  : ∀ {k A A′} (q : k < A′) (e : A ≈ A′) → BkOK (res⁻O q e)
R-trC  : ∀ {B k A A′ ξ} (P : Cp k A) (e : A ≈ A′) (z : Vc A P ξ) {ẑ : Ordˢ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (trC P e z)) (valC (trC P e z))) ẑ
R-tr⁻C : ∀ {B k A A′ ξ} (P : Cp k A′) (e : A ≈ A′) (z : Vc A′ P ξ) {ẑ : Ordˢ B} → Rs B (outC P z) ẑ → Rs B (outC (posC (tr⁻C P e z)) (valC (tr⁻C P e z))) ẑ
R-trV  : ∀ {B k A A′ ξ} (R : Strict k A) (e : A ≈ A′) (z : Vs A R ξ) {ẑ : Ordˢ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (trV R e z)) (valW (trV R e z))) ẑ
R-tr⁻V : ∀ {B k A A′ ξ} (R : Strict k A′) (e : A ≈ A′) (z : Vs A′ R ξ) {ẑ : Ordˢ B} → Rs B (outV R z) ẑ → Rs B (outV (posW (tr⁻V R e z)) (valW (tr⁻V R e z))) ẑ

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
     (λ ξ em′ z ẑ l → R-trO e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (resO r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (resO r e)) z))
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
     (λ ξ em′ z ẑ l → R-tr⁻O e (subst (λ u → Rs B (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (res⁻O r e)) z))
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

R-trL⁻ : ∀ {B A A′ π} (d : Lk A A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trL⁻ d x) ŷ
R-trL⁻ (inj₁ e) r = R-tr⁻O e r
R-trL⁻ (inj₂ refl) r = r

R-trL : ∀ {B A A′ π} (d : Lk A A′) {x : O A π} {ŷ : Ordˢ B} → Rs B x ŷ → Rs B (trL d x) ŷ
R-trL (inj₁ e) r = R-trO e r
R-trL (inj₂ refl) r = r
```

**右边.** `Ordˢ` 上的搬运.

```agda
R-trˢ  : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ a} → Rs a x ŷ → Rs b x (trˢ e ŷ)
R-tr⁻ˢ : ∀ {a b A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ b} → Rs b x ŷ → Rs a x (tr⁻ˢ e ŷ)
R-bkˢ  : ∀ {j a b A ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (resˢ q e))} → Rs (repˢ (resˢ q e)) z ẑ → Rs j z (backˢ (resˢ q e) ẑ)
R-bk⁻ˢ : ∀ {j a b A ξ} (q : j <ᴵ b) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (res⁻ˢ q e))} → Rs (repˢ (res⁻ˢ q e)) z ẑ → Rs j z (backˢ (res⁻ˢ q e) ẑ)

R-trˢ e rz = rz
R-trˢ e (rs r) = rs (R-trˢ e r)
R-trˢ e (rl h) = rl (λ n → R-trˢ e (h n))
R-trˢ e (rwk r) = rwk (R-trˢ e r)
R-trˢ e (rcv r) = rcv (R-trˢ e r)
R-trˢ (s≅ e) (rmk zero l r) = rmk zero (R-trˢ e l) (R-trˢ (s≅ e) r)
R-trˢ (l≅ h) (rmk (self n) l r) = rmk (self n) (R-trˢ (h n) l) (R-trˢ (l≅ h) r)
R-trˢ (s≅ e) (rup zero l) = rup zero (R-trˢ e l)
R-trˢ (l≅ h) (rup (self n) l) = rup (self n) (R-trˢ (h n) l)
R-trˢ {b = b} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (resˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (resˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs b (h₁ ξ (intoU r z)) (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) ẑ))
                             (R-trˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bkˢ q e (outR (<→◃ (ltˢ (resˢ q e))) l))))))

R-tr⁻ˢ e rz = rz
R-tr⁻ˢ e (rs r) = rs (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rl h) = rl (λ n → R-tr⁻ˢ e (h n))
R-tr⁻ˢ e (rwk r) = rwk (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rcv r) = rcv (R-tr⁻ˢ e r)
R-tr⁻ˢ (s≅ e) (rmk zero l r) = rmk zero (R-tr⁻ˢ e l) (R-tr⁻ˢ (s≅ e) r)
R-tr⁻ˢ (l≅ h) (rmk (self n) l r) = rmk (self n) (R-tr⁻ˢ (h n) l) (R-tr⁻ˢ (l≅ h) r)
R-tr⁻ˢ (s≅ e) (rup zero l) = rup zero (R-tr⁻ˢ e l)
R-tr⁻ˢ (l≅ h) (rup (self n) l) = rup (self n) (R-tr⁻ˢ (h n) l)
R-tr⁻ˢ {a = a} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (res⁻ˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (res⁻ˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs a (h₁ ξ (intoU r z)) (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) ẑ))
                             (R-tr⁻ˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bk⁻ˢ q e (outR (<→◃ (ltˢ (res⁻ˢ q e))) l))))))

R-bkˢ zero (s≅ e) l = R-tr⁻ˢ e l
R-bkˢ (suc q) (s≅ e) l = R-bkˢ q e l
R-bkˢ (lim n q) (l≅ h) l = R-bkˢ q (h n) l

R-bk⁻ˢ zero (s≅ e) l = R-trˢ e l
R-bk⁻ˢ (suc q) (s≅ e) l = R-bk⁻ˢ q e l
R-bk⁻ˢ (lim n q) (l≅ h) l = R-bk⁻ˢ q (h n) l
```

## §5 嵌入, $\dot\Omega$

`R-ι`: 嵌入不改对面的树. `omk` 的一行: 输入的 $z$ 与对面的 $\hat y'$ 有关系, 输出的 $x$ 是 $z$ 嵌到规范位置, 所以记号的两半都还在.

```agda
out-intoC : ∀ {L k} (P : Cp k L) {ξ} (z : O k ξ) → outC P (intoC P z) ≡ z
out-intoC Lv.self z = refl
out-intoC (Lv.suc P) z = out-intoC P z
out-intoC (Lv.lim n P) z = out-intoC P z
out-intoC (Lv.fst P) z = out-intoC P z
out-intoC (Lv.bra η e P) z = out-intoC P z

out-intoV : ∀ {L k} (R : Strict k L) {ξ} (z : O k ξ) → outV R (intoV R z) ≡ z
out-intoV (st-suc P) z = out-intoC P z
out-intoV (st-lim n P) z = out-intoC P z
out-intoV (st-fst P) z = out-intoC P z
out-intoV (st-bra η e P) z = out-intoC P z

cv-into : ∀ {k a b} (P : Cp a b) (s : k < a) {ξ} (z : O k ξ) → outU s (cvP P s (intoU (P ◁ s) z)) ≡ z
cv-into Lv.self s z = out-intoU s z
cv-into (Lv.suc P) s z = cv-into P s z
cv-into (Lv.lim n P) s z = cv-into P s z
cv-into (Lv.fst P) s z = cv-into P s z
cv-into (Lv.bra η e P) s z = cv-into P s z

lk≈ : ∀ {k rep j} → Lk k rep → k ≈ ⌜ j ⌝ → rep ≈ ⌜ j ⌝
lk≈ (inj₁ e) d = ≈-trans (≈-sym e) d
lk≈ (inj₂ refl) d = d

BLOK : ∀ {k a b} {r : k < a} → RL r b → Set
BLOK w = ∀ {B ξ} {z : O (repL w) ξ} {ẑ : Ordˢ B} → Rs B z ẑ → Rs B (backL w z) ẑ

R-bL : ∀ {k a b} (r : k < a) (d : Lk a b) → BLOK (resL r d)
R-bL r (inj₁ e) with resO r e | R-bk r e
... | restrO d′ l t b | H = H
R-bL r (inj₂ refl) = λ l → l

module EmbR (L : LG) (tc : Tc L) where
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

  R-ι : ∀ {B a a′ π} (P : Cp a′ L) (d : Lk a a′) {z : O a π} {ŷ : Ordˢ B} → Rs B z ŷ → Rs B (ι a P d z) ŷ
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
       (λ ξ em′ z ẑ l → rwk (R-ι P d (subst (λ w → Rs B (h₁ ξ (intoU r (b w))) (f (intoˢ (<→◃ q) ẑ))) (sym (cv-into P s z))
                                             (h ξ em′ (b z) ẑ (intoR (<→◃ q) (H (outR (<→◃ q) l)))))))

RΩ̇ : ∀ i {t} → t ≈ ⌜ i ⌝ → (tc : Tc t) → Rs i (Ω̇ t tc) (Ωˢ i)
RΩ̇ zero Lv.z≈ tc = rs rz
RΩ̇ (suc b) {t = Lv.suc t′} (Lv.s≈ e) tc =
  rΩ Lv.zero tt zero e (λ ξ em′ z ẑ l → rmk zero l (rup zero (EmbR.R-ι (Lv.suc t′) tc (Lv.suc Lv.self) (inj₂ refl) l)))
RΩ̇ (lim g s) {t = Lv.lim f′} (Lv.l≈ h) tc =
  rl (λ n → rwk (rmk (self n) (RΩ̇ (g n) (h n) (tc n)) (rup (self n) (EmbR.R-ι (Lv.lim f′) tc (Lv.lim n Lv.self) (inj₂ refl) (RΩ̇ (g n) (h n) (tc n))))))
```
