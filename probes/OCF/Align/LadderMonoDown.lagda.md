# 跨高度单调 (二): `ι↓ x` 与 `ι↓ (ι↓ x′)`

> 结论写在 [LadderMono](LadderMono.lagda.md). **`D-ι↓`: 对任何 `Rq n k k′ x x′`, `ι↓ x` 与 `ι↓ (ι↓ x′)` 有 `Dn`.** `ι↓` 把顶层 `qΩ` 变成高度 $n$ 的 `qΩ↓`, 把 `omk r z x` 变成 `ι↓ z`, 所以左右都读 $z$; 这里用不到 `x = ι r z`. 行与 [LadderNFRel](LadderNFRel.lagda.md) 的 `R-ι↓`, `R-tl` 一一对应. **`D-self`: `Ω̇ m zero` 与 `ι↓ (Ω̇ m zero)` 有 `Dn`, 对一切 $m$.** 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoDown where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; flo; cvFlo; _∼ᶠ_; ⊔∼; fk∼; ∼ᶠ-refl)
open import OCF.Align.LadderNFTree
open import OCF.Align.LadderNFRel
open import OCF.Align.LadderMonoRel
```

## §1 `Rq` 到 `Dn`

```agda
Sim-dd : ∀ {χ ρ : Fv} {x y w} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ (suc n) (upd χ n x) (upd (upd ρ n y) (suc n) w)
Sim-dd {χ} {ρ} {x} {y} {w} n s c i r = subst (upd χ n x i ∼ᶠ_) (sym (upd-lt (upd ρ n y) w r)) (upd∼ n s c i r)

D-ι↓ : ∀ {n k k′ α α′ α₁ φ ψ χ ρ} → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Dn (suc n) α α′ (ι↓ x) (ι↓ {α = α′} (ι↓ {α = α₁} x′))
D-ι↓ ek rz = dz
D-ι↓ {n = n} ek (rs sa sb r) = ds sa (Sim-dd n sb (flo-∼ ek)) (D-ι↓ ek r)
D-ι↓ ek (rl h) = dl (λ n → D-ι↓ ek (h n))
D-ι↓ ek (ri e h) = di e (λ x y d → D-ι↓ ek (h x y d))
D-ι↓ ek (rŝ e r h) = dŝ e (D-ι↓ ek r) (λ η ee η′ e′ d → D-ι↓ ek (h η ee η′ e′ d))
D-ι↓ ek (rĉ e dz′ dg r h) = dĉ e dz′ dg (D-ι↓ ek r) (λ η ee η′ e′ d → D-ι↓ ek (h η ee η′ e′ d))
D-ι↓ ek (rclo s r h) = dclo s (D-ι↓ ek r) (λ η η′ d → D-ι↓ ek (h η η′ d))
D-ι↓ ek (rcl {q = q} same s r h) = dcl {q = suc q} s (D-ι↓ ek r) (λ η η′ d → dwkˡ (dwkʳ (dwkʳ (D-ι↓ ek (h η η′ d)))))
D-ι↓ ek (rwkˡ r) = dwkˡ (D-ι↓ ek r)
D-ι↓ ek (rwkʳ r) = dwkʳ (D-ι↓ ek r)
D-ι↓ {n = n} ek (rΩ↓ {q = q} same ei s c f) = dΩ↓ {q = suc q} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ (D-ι↓ ek (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l))))))
D-ι↓ {n = n} ek (rΩ {r = r} {r′ = r′} ei s c f) = dΩ↓ {q = zero} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ (D-ι↓ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l))))))
D-ι↓ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = dwkˡ (dwkʳ (D-ι↓ ea l))
D-ι↓ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = dwkˡ (dwkʳ (D-ι↓ ea l))
```

## §2 根层: `tl`

`Ω̇ 0 zero` 没有 `ι↓` 在里面, 所以这里单独走 `tl`. 同 `R-tl`, `R-tlΩ`.

```agda
D-tl : ∀ {c c′ α₁ k₁ k₂ χ ρ} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Dn 0 c c′ (tl {χ = χ} (flo k₁) cv a) (ι↓ {k = α₁} (tl {χ = ρ} (flo k₂) cv′ b))
D-tl z≅ = dz
D-tl (s≅ le e) = ds (flo-∼ le) (λ i ()) (D-tl e)
D-tl (l≅ h) = dl (λ n → D-tl (h n))
D-tl (lᵢ≅ {p = q} e h) = di e (λ x y dd → D-tl (h x y (≅→Rˢ (<→◃ q) dd)))
D-tl {k₁ = suc k′} (upˡ {r = zero} d) = dwkˡ (D-tl d)
D-tl {k₁ = lim f s} (upˡ {r = self n} d) = dwkˡ (D-tl d)
D-tl {k₂ = suc k′} (upʳ {r = zero} d) = dwkʳ (D-tl d)
D-tl {k₂ = lim f s} (upʳ {r = self n} d) = dwkʳ (D-tl d)
D-tl {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  dĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl (ĉ≅ ec dt dg eo eO) = dĉ ec dt dg (D-tl eo) (λ η e η′ e′ eη → D-tl (eO η e η′ e′ eη))

D-tlΩ : ∀ {c c′ α₁ η η′ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Dn 0 c c′ (tl {χ = χ} φ cv (Ωˢ η)) (ι↓ {k = α₁} (tl {χ = ρ} φ′ cv′ (Ωˢ η′)))
D-tlΩ z≅ s = ds s (λ i ()) dz
D-tlΩ (s≅ e) s = di e (λ x y d → dwkˡ (dwkʳ (D-tl d)))
D-tlΩ (l≅ h) s = dl (λ n → dwkˡ (dwkʳ (D-tl (Ωˢ-≅ (h n)))))
```

## §3 `Ω̇ m zero`

```agda
D-self : ∀ m {α} → Dn m zero α (Ω̇ m zero) (ι↓ (Ω̇ m zero))
D-self zero =
  dclo (∼ᶠ-refl fz)
    (D-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
    (λ η η′ eη → D-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
D-self (suc m) =
  dcl {q = zero} (∼ᶠ-refl fz)
    (dwkˡ (dwkʳ (D-ι↓ (s≅ z≅) (RΩ̇ m (s≅ z≅)))))
    (λ η η′ eη → dwkˡ (dwkʳ (dwkʳ (D-ι↓ eη (RΩ̇ m eη)))))
```
