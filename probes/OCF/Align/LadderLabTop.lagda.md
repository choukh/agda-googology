# 高度上的标签 (四): 贴到证书的计值上

> **判决: HOLDS (编译过, 对一切 `HtS`, `PxS`; 条件只有标准形, 写成前提).** 结论写在 [LadderLab](LadderLab.lagda.md). `label-tree`: 树的折叠 `Tᵠ m α` 带标签 $\psi_0(\Omega_{P\,m\,\theta})$. `label-cert`: 证书 `GᴺTᵠ m α` 的计值带同一个标签. 前提 `NF₁` $\psi_0(\Omega_{P\,m\,\theta})$ 在实例上由 `NF-Ωᵐ`, `NF-ψ` 给 ([LadderLabAccept](LadderLabAccept.lagda.md)).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderLabBase
module OCF.Align.LadderLabTop (𝕊 : HtS) (𝕏 : PxS 𝕊) where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.Level
import OCF.Align.EBO as E
open E using (T; Ωt)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.LadderLabZUniform3Base using (Ev; Lab₀; ψ₀ᵗ)
open import OCF.Align.LadderLabZUniform4Base using (Fl)
open import OCF.Align.LadderLabZUniform5Class using (hon)
open import OCF.Align.LadderLabZPrefix using (toZ)
open import OCF.Align.LadderLabZNFWForce
open import OCF.Align.LadderLabZNFWEq using (_≅ᶻ_; toZ-≅)
open import OCF.Align.LadderLabForget using (same)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabZInfWMain 𝕊 using (GᴺTᵠ)
import OCF.Align.LadderLabZInfWRel 𝕊 as W
open import OCF.Align.LadderLabClass 𝕊 𝕏 using (LqΩ̇)
open import OCF.Align.LadderLabRel 𝕊 𝕏 using (RΩ̇)
open import OCF.Align.LadderLabEval 𝕊 𝕏 using (labelᵠ)
open PxS 𝕏

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
