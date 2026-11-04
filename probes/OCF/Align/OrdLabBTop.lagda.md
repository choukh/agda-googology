> **机械改写, 验收用.** 由 [OrdLabTop](OrdLabTop.lagda.md) 经 `Survey/scripts/ordlab/mk_b.py` 生成: 只把 `HtS`, `PxS`, `LadderInf*` 换成 `HtB`, `PxB`, `LadderOrd*`. 见 [OrdLab](OrdLab.lagda.md).

# OrdLabBTop

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
open import OCF.Align.OrdLabBBase
module OCF.Align.OrdLabBTop (𝕊 : HtB) (𝕏 : PxB 𝕊) where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.OrdLabZLevel
import OCF.Align.EBO as E
open E using (T; Ωt)
open import OCF.Align.OrdLabZCorrespond using (Lab; Lab-≅)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.OrdLabZUniform3Base using (Ev; Lab₀; ψ₀ᵗ)
open import OCF.Align.OrdLabZUniform4Base using (Fl)
open import OCF.Align.OrdLabZUniform5Class using (hon)
open import OCF.Align.OrdLabZPrefix using (toZ)
open import OCF.Free.Force
open import OCF.Free.Eq using (_≅ᶻ_; toZ-≅)
open import OCF.Align.OrdLabForget using (same)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
import OCF.Align.LadderOrdRel 𝕊 as W
open import OCF.Align.OrdLabBClass 𝕊 𝕏 using (LqΩ̇)
open import OCF.Align.OrdLabBRel 𝕊 𝕏 using (RΩ̇)
open import OCF.Align.OrdLabBEval 𝕊 𝕏 using (labelᵠ)
open PxB 𝕏

label-tree : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψ₀ᵗ (Ωt (P m θ))) → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ m α ev p) (ψ₀ᵗ (Ωt (P m θ)))
label-tree m Y hY lY nθ nf e = labelᵠ (LqΩ̇ m Y hY lY nθ e hon) (RΩ̇ m (≅ᴵ-refl _)) ok₀ (λ i h r → ok₀ i) nf

selfT : ∀ m α {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → toZ (Tᵠ m α ev p) ≅ᶻ toZ (Tᵠ m α ev p)
selfT m α ev p = toZ-≅ (W.R→≈ᵠ (W.RΩ̇ m (≅ᴵ-refl α)) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev p ev p (≅ᴵ-refl zero))

label-cert : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψ₀ᵗ (Ωt (P m θ))) → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ m α ev p)) (ψ₀ᵗ (Ωt (P m θ)))
label-cert m Y hY lY nθ nf {α} e ev p = Lab-≅ (same (selfT m α ev p) (GᴺTᵠ m α ev p) (proj₁ L)) (proj₂ L)
  where L = label-tree m Y hY lY nθ nf e ev p
```
