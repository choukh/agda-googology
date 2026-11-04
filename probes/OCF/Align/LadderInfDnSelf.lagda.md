# 高度抽象: `ι↓ (Ω̇ m 0)` 的值就是 `Ω̇ m 0` 的值

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderInf](LadderInf.lagda.md). 从 [LadderMonoDown](LadderMonoDown.lagda.md) 改写, $m+1$ 换成任意 `δ : m <ᴸ m′`, 第 0 行按 `view` 分三种. 对高度结构的每个高度成立, 不递归于高度.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfDnSelf (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; flo; cvFlo; _∼ᶠ_; ⊔∼; fk∼; fz∼; ∼ᶠ-refl)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderInfTree 𝕊
open import OCF.Align.LadderInfRel 𝕊
open import OCF.Align.LadderInfDn 𝕊

Sim-dd : ∀ {m} {χ ρ : Fv} {x y w} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ m (cap χ n x) (cap (cap ρ n y) m w)
Sim-dd {m} {χ} {ρ} {x} {y} {w} n s c i r = subst (cap χ n x i ∼ᶠ_) (sym (cap-lt (cap ρ n y) w r)) (cap∼ n s c i r)

D-ι↓ : ∀ {n m m′ k k′ α α′ α₁ φ ψ χ ρ} (q₁ : n <ᴸ m) (δ : m <ᴸ m′) → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Dn δ α α′ (ι↓ q₁ x) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ x′))
D-ι↓ q₁ δ ek rz = dz
D-ι↓ {n = n} q₁ δ ek (rs sa sb r) = ds sa (Sim-dd n sb (flo-∼ ek)) (D-ι↓ q₁ δ ek r)
D-ι↓ q₁ δ ek (rl h) = dl (λ n → D-ι↓ q₁ δ ek (h n))
D-ι↓ q₁ δ ek (ri e h) = di e (λ x y d → D-ι↓ q₁ δ ek (h x y d))
D-ι↓ q₁ δ ek (rŝ e r h) = dŝ e (D-ι↓ q₁ δ ek r) (λ η ee η′ e′ d → D-ι↓ q₁ δ ek (h η ee η′ e′ d))
D-ι↓ q₁ δ ek (rĉ e dz′ dg r h) = dĉ e dz′ dg (D-ι↓ q₁ δ ek r) (λ η ee η′ e′ d → D-ι↓ q₁ δ ek (h η ee η′ e′ d))
D-ι↓ q₁ δ ek (rclo s r h) = dclo s (D-ι↓ q₁ δ ek r) (λ η η′ d → D-ι↓ q₁ δ ek (h η η′ d))
D-ι↓ q₁ δ ek (rcl {q = q} same s r h) = dcl {q = tr< q q₁} s (D-ι↓ q₁ δ ek r) (λ η η′ d → dwkˡ (dwkʳ (dwkʳ (D-ι↓ q₁ δ ek (h η η′ d)))))
D-ι↓ q₁ δ ek (rwkˡ r) = dwkˡ (D-ι↓ q₁ δ ek r)
D-ι↓ q₁ δ ek (rwkʳ r) = dwkʳ (D-ι↓ q₁ δ ek r)
D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ δ ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c f) =
  dΩ↓ {q = tr< q q₁} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ
    (subst₂ (λ u v → Dn δ α α′ (ι↓ q₁ (h ξ ζ (intoV q u))) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoV q v)))))
       (sym (out-intoV (tr< q q₁) z))
       (sym (trans (cong (λ w → outV (tr< q q₁) (intoV (tr< q q₁) w)) (out-intoV (tr< (tr< q q₁) δ) z′)) (out-intoV (tr< q q₁) z′)))
       (D-ι↓ q₁ δ ek (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l)))))))
D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ δ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  dΩ↓ {q = q₁} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ
    (subst₂ (λ u v → Dn δ α α′ (ι↓ q₁ (h ξ ζ (intoU (<→◃ r) u))) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))
       (sym (out-intoV q₁ z))
       (sym (trans (cong (λ w → outV q₁ (intoV q₁ w)) (out-intoV (tr< q₁ δ) z′)) (out-intoV q₁ z′)))
       (D-ι↓ q₁ δ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l)))))))
D-ι↓ q₁ δ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = dwkˡ (dwkʳ (D-ι↓ q₁ δ ea l))
D-ι↓ q₁ δ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = dwkˡ (dwkʳ (D-ι↓ q₁ δ ea l))

D-tl : ∀ {m′} (δ : h₀ <ᴸ m′) {c c′ α₁ k₁ k₂ χ ρ} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Dn δ c c′ (tl {χ = χ} (flo k₁) cv a) (ι↓ {k = α₁} δ (tl {χ = ρ} (flo k₂) cv′ b))
D-tl δ z≅ = dz
D-tl δ (s≅ le e) = ds (flo-∼ le) (λ i q → ⊥-elim (no< q)) (D-tl δ e)
D-tl δ (l≅ h) = dl (λ n → D-tl δ (h n))
D-tl δ (lᵢ≅ {p = q} e h) = di e (λ x y dd → D-tl δ (h x y (≅→Rˢ (<→◃ q) dd)))
D-tl δ {k₁ = suc k′} (upˡ {r = zero} d) = dwkˡ (D-tl δ d)
D-tl δ {k₁ = lim f s} (upˡ {r = self n} d) = dwkˡ (D-tl δ d)
D-tl δ {k₂ = suc k′} (upʳ {r = zero} d) = dwkʳ (D-tl δ d)
D-tl δ {k₂ = lim f s} (upʳ {r = self n} d) = dwkʳ (D-tl δ d)
D-tl δ {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  dĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (D-tl δ et) (λ η e η′ e′ eη → D-tl δ (eg η e η′ e′ eη))
D-tl δ {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl δ {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl δ {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl δ {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl δ {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl δ et) (λ η e η′ e′ eη → D-tl δ (eg η e η′ e′ eη))
D-tl δ {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl δ et) (λ η e η′ e′ eη → D-tl δ (eg η e η′ e′ eη))
D-tl δ {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl δ et) (λ η e η′ e′ eη → D-tl δ (eg η e η′ e′ eη))
D-tl δ {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl δ et) (λ η e η′ e′ eη → D-tl δ (eg η e η′ e′ eη))
D-tl δ (ĉ≅ ec dt dg eo eO) = dĉ ec dt dg (D-tl δ eo) (λ η e η′ e′ eη → D-tl δ (eO η e η′ e′ eη))

D-tlΩ : ∀ {m′} (δ : h₀ <ᴸ m′) {c c′ α₁ η η′ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Dn δ c c′ (tl {χ = χ} φ cv (Ωˢ η)) (ι↓ {k = α₁} δ (tl {χ = ρ} φ′ cv′ (Ωˢ η′)))
D-tlΩ δ z≅ s = ds s (λ i q → ⊥-elim (no< q)) dz
D-tlΩ δ (s≅ e) s = di e (λ x y d → dwkˡ (dwkʳ (D-tl δ d)))
D-tlΩ δ (l≅ h) s = dl (λ n → dwkˡ (dwkʳ (D-tl δ (Ωˢ-≅ (h n)))))

D-rowL : ∀ {m m′ α} (δ : m <ᴸ m′) F (qs₁ : ∀ i → F i <ᴸ m) → ∀ i → Dn δ zero α (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i) (ι↓ {k = zero} δ (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i))
D-rowL δ F qs₁ zero = dwkˡ (dwkʳ (ds fz∼ (λ i q → subst (fz ∼ᶠ_) (sym (cap-lt (κ fz) fz q)) fz∼) dz))
D-rowL {m} {α = α} δ F qs₁ (suc i) =
  subst (λ X → Dn δ zero α (stepL (qs₁ i) X) (ι↓ {k = zero} δ (stepL (qs₁ i) X))) (sym (ΩI≡ (qs₁ i)))
    (dwkˡ (dwkʳ (D-ι↓ (qs₁ i) δ z≅ (RΩ̇ (F i) z≅))))

D-row : ∀ {m m′ α} (δ : m <ᴸ m′) (v : View _<ᴸ_ h₀ m) → Dn δ zero α (rowV m (ΩI m) v) (ι↓ {k = zero} δ (rowV m (ΩI m) v))
D-row δ base =
  dclo (∼ᶠ-refl fz)
    (D-tlΩ δ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
    (λ η η′ eη → D-tlΩ δ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
D-row {m} {α = α} δ (clos {n = n} q) =
  subst (λ X → Dn δ zero α (rowC q X) (ι↓ {k = zero} δ (rowC q X))) (sym (ΩI≡ q))
    (dcl {q = q} (∼ᶠ-refl fz)
      (dwkˡ (dwkʳ (D-ι↓ q δ (s≅ z≅) (RΩ̇ n (s≅ z≅)))))
      (λ η η′ eη → dwkˡ (dwkʳ (dwkʳ (D-ι↓ q δ eη (RΩ̇ n eη))))))
D-row δ (chain F qs₁) = dl (D-rowL δ F qs₁)

D-self : ∀ {m m′ α} (δ : m <ᴸ m′) → Dn δ zero α (Ω̇ m zero) (ι↓ {k = zero} δ (Ω̇ m zero))
D-self {m} δ = D-row δ (view m)
```
