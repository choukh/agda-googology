# 不带高度的树接上带高度的树 (四): 左边的嵌入, $\dot\Omega$

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). `R-ιL`: 左边的 `ι` 不改右边的树 (右边的 `ι` 单独由 `R-ιQ` 给, [WeakBridgeRel](WeakBridgeRel.lagda.md)). 这样 `cm` 这一行只要: $z\sim\hat z$ 经归纳成 $\iota z\sim\hat z$, 再用 `R-ap` 做右边的运算. `fromRs`: 低层的 `Rs` 进 `C`. `RΩ̇⁺`: $\dot\Omega$, 对一切 $\theta$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; Ωˢ)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo)
import OCF.Free.Tree as FT
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; Emp; ZB; out-intoV; cv-into)
open import OCF.Align.GuardTightCert using (c₁)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁)
open import OCF.Align.GuardCertRel using (Hr; rz; rs; rl; rwk; rcv; rmk; rΩ; rŝ; rĉ; rĉŝ; Rz; RΩ̇; le-emp; intoR; module EmbR; R-bL; BLOK; lk≈′)
open import OCF.Align.GuardCertNf using (lc-absurd)
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeNf using (hp⁺; one)
open import OCF.Align.WeakBridgeRel
open import OCF.Align.WeakBridgeC
open CR using (Rs; fr; gd)
open import OCF.Align.WeakBridgeOp
open import OCF.Align.WeakBridgeTr
open I using (q0; qs; ql; qi; qŝ; qĉ; qclo; qwk; qΩ)
```

## §1 `fromRs`

```agda
cv-of : ∀ {π k₀ φ} → (∀ f → Mem π f → fη f ⊑ᴵ k₀) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) → CvL π φ
cv-of c cv f m e = ⊑ᴵ-trans (c f m) (Sim→⊑ᴵ (cv e))

fromRs : ∀ {M k₀ m A π φ c χ} {x : O A π} {ŷ : Ordˢ k₀} (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) → Nz A → Rs k₀ m x ŷ → C M x (I.tl {m = 0} {c = c} {χ = χ} φ cv ŷ)
fromRs cv n rz = cz
fromRs cv n (rs a c r) = cs (cv-of c cv) (fromRs cv n r)
fromRs cv n (rl h) = cl (λ i → fromRs cv n (h i))
fromRs cv n (rwk r) = cwl (fromRs cv n r)
fromRs cv n (rcv r) = cvl (fromRs cv n r)
fromRs {k₀ = suc k′} {m = m₀} cv n (rmk zero dk l iv r) = cml {m₀ = m₀} zero cv []ᵒ (rmk zero dk l iv r) ≃id (cwr (fromRs (cvFlo k′) n r))
fromRs {k₀ = lim g s} {m = m₀} cv n (rmk (self i) dk l iv r) = cml {m₀ = m₀} (self i) cv []ᵒ (rmk (self i) dk l iv r) ≃id (cwr (fromRs (cvFlo (g i)) n r))
fromRs cv n (rΩ r _ q dk prem) = ci r dk (λ ξ em z ẑ l → fromRs cv n (prem ξ em z ẑ (intoR (<→◃ q) l)))
fromRs {k₀ = suc _} cv n (rŝ z ec rt rg) = cŝ n ec (fromRs cv n rt) (λ η e e′ → fromRs cv n (rg η e e′))
fromRs {k₀ = lim _ _} cv n (rŝ z ec rt rg) = cŝ n ec (fromRs cv n rt) (λ η e e′ → fromRs cv n (rg η e e′))
fromRs {k₀ = zero} {A = Lv.suc _} cv n (rŝ () ec rt rg)
fromRs {k₀ = zero} {A = Lv.lim _} cv n (rŝ () ec rt rg)
fromRs {k₀ = zero} {A = Lv.lc _ _ _} cv n (rŝ () ec rt rg)
fromRs {k₀ = zero} {A = Lv.zero} cv () (rŝ z ec rt rg)
fromRs cv n (rĉ ec dz dg ro rg) = cĉ ec dz dg (fromRs cv n ro) (λ η e e′ → fromRs cv n (rg η e e′))
fromRs {k₀ = zero} cv n (rĉŝ tt ec rt rg₀ ro rg) = cĉ ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (fromRs cv n ro) (λ η e e′ → fromRs cv n (rg η e e′))
```

## §2 左边的嵌入

`P` 无分支时地板不变 (`Emp (pF P)`). 位置在 `c⁺ θ` 里: 节点是高层就无分支 (`nb⁺`).

```agda
cvL-pl : ∀ {π ρ φ} → CvL π φ → Emp ρ → CvL (π ∪ ρ) φ
cvL-pl c em f (ml m) e = c f m e
cvL-pl c em f (mr m) e = ⊥-elim (em m)

hr-emp : ∀ {m a c} {P : Cp a c} {B} → Emp (pF P) → Hr m P B
hr-emp {m = fr} em = le-emp em
hr-emp {m = gd} em = λ _ → le-emp em

module EmbC (θ : Ordᴵ) where
  L : LG
  L = c⁺ θ

  tc : Tc L
  tc = tc⁺ θ

  open Emb L tc
  open EmbR L tc (hp⁺ θ)

  em-hi : ∀ {a j} {P : Cp a L} → a ≈ c⁺ j → Emp (pF P)
  em-hi {P = P} e m = emp-nb (nb⁺ θ P (NF-hi e)) m

  BLC : ∀ {k a b} {r : k < a} → RL r b → Set
  BLC w = ∀ {M ξ B φ χ} {z : O (repL w) ξ} {ẑ : QQ B φ χ} → C M z ẑ → C M (backL w z) ẑ

  C-bL : ∀ {k a b} (r : k < a) (d : Lk a b) → BLC (resL r d)
  C-bL r (inj₁ e) with resO r e | Cf-bk r e
  ... | restrO d′ l t b | H = H
  C-bL r (inj₂ refl) = λ l → l

  R-ιL : ∀ {M a a′ π B φ χ} (P : Cp a′ L) (d : Lk a a′) → Emp (pF P) → {x : O a π} {y : QQ B φ χ} → C M x y → C M (ι a P d x) y
  R-ιLC : ∀ {M i a a′ π B φ χ} (s : i ◃ M) (P : Cp a′ L) (d : Lk a a′) → Emp (pF P) → {x : O a π} {y : QQ B φ χ} → LC M s x y → C i (ι a P d x) y

  R-ιLC zero P d em l = R-ιL P d em l
  R-ιLC (suc s) P d em l = R-ιLC s P d em l
  R-ιLC (self n) P d em l = R-ιL P d em l
  R-ιLC (lim n s) P d em l = R-ιLC s P d em l

  R-ιL P d em cz = cz
  R-ιL P d em (cs c D) = cs (cvL-pl c em) (R-ιL P d em D)
  R-ιL P d em (cl h) = cl (λ n → R-ιL P d em (h n))
  R-ιL P d em (cwl D) = cwl (R-ιL P d em D)
  R-ιL P d em (cvl D) = cvl (R-ιL P d em D)
  R-ιL P d em (cwr D) = cwr (R-ιL P d em D)
  R-ιL P d em (cdr D) = cdr (R-ιL P d em D)
  R-ιL {M = M} {a = a} P d em (cm {R = R} {z = z} {ẑ = ẑ} s l dk lr E D) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r′ =
    cvl (cm s l (lk≈′ e₂ (lk≈′ e dk))
            (intoL s (subst (λ w → C _ w ẑ) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (Cf-trL (lkC e e₂) (outL s lr))))
            E
            (subst (λ w → C M w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z))
                   (Tᴿ (R-ap l (C-up s (R-ιLC s (stCp pos) (lkC e e₂) (em-hi {P = stCp pos} (lk≈′ e₂ (lk≈′ e dk))) lr))) E)))
  R-ιL P d em (cml r cv l p E D) = Tᴿ (R-ap l (fromRs cv (nz-c θ) (R-ι P d (hr-emp em) p))) E
  R-ιL {M = M} {a = a} P d em (ci r {h = h₁} {f = f} dk prem) with resL r d | R-bL r d
  ... | rl e′ s u b | H′ =
    ci (P ◁ s) (lk≈′ e′ dk) (λ ξ emξ z ẑ l → cwl (R-ιL P d em
         (subst (λ w → C M (h₁ ξ (intoU r (b w))) (f ẑ)) (sym (cv-into P s z)) (prem ξ emξ (b z) ẑ (H′ l)))))
  R-ιL {M = M} {a = a} P d em (cΩ r q {h = h₁} {f = f} dk e₂ q₂ c prem) with resL r d | C-bL r d
  ... | rl e′ s u b | H′ =
    cΩ (P ◁ s) q (lk≈′ e′ dk) e₂ q₂ (cvL-pl c em) (λ ξ ξ̂ ζ cv z ẑ l → cwl (R-ιL P d em
         (subst (λ w → C M (h₁ ξ (intoU r (b w))) (f ξ̂ ζ (I.intoU (<→◃ q) ẑ))) (sym (cv-into P s z)) (prem ξ ξ̂ ζ cv (b z) ẑ (intoL (<→◃ q₂) (H′ (outL (<→◃ q₂) l)))))))
  R-ιL {a = Lv.zero} P d em (cŝ () ec rt rg)
  R-ιL {a = Lv.suc _} P d em (cŝ n ec rt rg) = cŝ (nz-c θ) ec (R-ιL P d em rt) (λ η e e′ → R-ιL P d em (rg η e e′))
  R-ιL {a = Lv.lim _} P d em (cŝ n ec rt rg) = cŝ (nz-c θ) ec (R-ιL P d em rt) (λ η e e′ → R-ιL P d em (rg η e e′))
  R-ιL {a = Lv.lc _ _ _} P d em (cŝ n ec rt rg) = cŝ (nz-c θ) ec (R-ιL P d em rt) (λ η e e′ → R-ιL P d em (rg η e e′))
  R-ιL P d em (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-ιL P d em ro) (λ η e e′ → R-ιL P d em (rg η e e′))
  R-ιL P (inj₁ e) em (ccl {P = Q} c rt rg) with ≈-moveᴷ e Q
  ... | viaᴷ d′ Q′ u = ccl (cvL-pl c em) (R-ιL P (inj₁ e) em rt) (λ η e′ → cwl (R-ιL P (inj₁ e) em (rg η e′)))
  R-ιL P (inj₂ refl) em (ccl c rt rg) = ccl (cvL-pl c em) (R-ιL P (inj₂ refl) em rt) (λ η e′ → cwl (R-ιL P (inj₂ refl) em (rg η e′)))
```

## §3 $\dot\Omega$

右边是 `I.Ω̇ 0 θ`. `view 0 = base`, 第 0 行是 `rowB`.

```agda
nz-one : ∀ {η} → one ⊑ᴵ η → ZB η → ⊥
nz-one {η = zero} (s⊑ _ ()) z

RΩ̇⁺ : ∀ {a j} → a ≅ᴵ j → C j (Ω̇ (c⁺ a) (tc⁺ a)) (I.Ω̇ 0 j)
RΩ̇⁺ z≅ =
  ccl (λ _ ())
      (cwl (fromRs proj₂ tt (EmbR.R-ι c₁ Tc-Ω₁ (hp⁺ zero) (Lv.fst Lv.self) (inj₂ refl) (λ _ _ ()) (RΩ̇ one (⌜≈⌝ (≅ᴵ-refl one)) (proj₁ (proj₂ Tc-Ω₁))))))
      (λ η e → cwl (fromRs (λ e₁ q → proj₂ e₁ (suc q)) tt (EmbR.R-ι c₁ Tc-Ω₁ (hp⁺ zero) (Lv.bra η e Lv.self) (inj₂ refl) (λ z → ⊥-elim (nz-one e z)) (RΩ̇ η (⌜≈⌝ (≅ᴵ-refl η)) (proj₂ (proj₂ Tc-Ω₁) η e)))))
RΩ̇⁺ {a = suc a} (s≅ d) =
  cΩ Lv.zero zero (c⁺-≈ d) (≅ᴵ-refl _) zero (λ _ ())
     (λ ξ ξ̂ ζ cv z ẑ l → cwr (cdr (cm zero (oι zero ∷ᵒ []ᵒ) (c⁺-≈ d) l ≃id
        (R-ιQ zero (C-up zero (EmbC.R-ιL (suc a) (Lv.suc Lv.self) (inj₂ refl) (λ ()) l))))))
RΩ̇⁺ {a = lim f s} (l≅ h) =
  cl (λ n → cwl (cdr (cm (self n) (oι (self n) ∷ᵒ []ᵒ) (c⁺-≈ (h n)) (RΩ̇⁺ (h n)) ≃id
       (R-ιQ (self n) (C-up (self n) (EmbC.R-ιL (lim f s) (Lv.lim n Lv.self) (inj₂ refl) (λ ()) (RΩ̇⁺ (h n))))))))

-- 节点是高层: 字面的 c⁺ a, 读法也是 tc⁺ a
data KH (θ : Ordᴵ) : ∀ {k} → k < c⁺ θ → Set where
  hiH : ∀ {a} (r : c⁺ a < c⁺ θ) → a <ᴵ θ → Tc-at r (tc⁺ θ) ≡ tc⁺ a → KH θ r

pullH : ∀ θ {k j} (r : k < c⁺ θ) → k ≈ c⁺ j → KH θ r
pullH zero r d = ⊥-elim (hic r d)
  where
  hic : ∀ {t j} → t < c₁ → t ≈ c⁺ j → ⊥
  hic q d′ with pull⁺ zero q
  ... | hi e ()
  ... | lo refl = lo≠hi (⌜≈⌝ (≅ᴵ-refl _)) d′
pullH (suc θ) Lv.zero d = hiH Lv.zero zero refl
pullH (suc θ) (Lv.suc r) d with pullH θ r d
... | hiH r q e = hiH (Lv.suc r) (suc q) e
pullH (lim f s) (Lv.lim n r) d with pullH (f n) r d
... | hiH r q e = hiH (Lv.lim n r) (lim n q) e

-- 折叠里出现的 Ω̇
ΩH : ∀ θ {t j} (q : t < c⁺ θ) → t ≈ c⁺ j → C j (Ω̇ t (Tc-at q (tc⁺ θ))) (I.Ω̇ 0 j)
ΩH θ q d with pullH θ q d
... | hiH r _ e rewrite e = RΩ̇⁺ (c⁺-≈⁻ d)
```
