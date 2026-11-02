# 统一折叠上的三层遗传好树 (五): $\psi_0(\Omega_\Omega\cdot2)$ 的验收

> 接 [UniformPendingGood](UniformPendingGood.lagda.md). 记号只在本文. 证书 `Gᴺ₂ᵁ` 的构造不读这里的任何东西; 验收用 `forceᴺ-≅` (计值与证书无关) 把 Uniform2Base 的标签搬到记号无关的计值树上, 再用 `Lab-uniq` 与 GoodL 的 `T2ᴸ` 比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPendingGoodAccept where

open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)

open import OCF.Align.Level
open import OCF.Align.Prefix using (toZ; Goodᶻ)
open import OCF.Align.UniformS using (toZ-≅)
open import OCF.Align.Uniform2Base using (Ev; Ω̂A; GA0-Ω̂; g0; GR; Lab₀; _⊔_; fk)
open import OCF.Align.Uniform2 using (good∅ᴿ)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2 using (Lab-uniq; t2)
open import OCF.Align.StandardOmega using (t2-NF)
open import OCF.Align.GoodL using (T2ᴸ; T2-label)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.UniformPendingGood using (Fl₁; P̂; rP̂; module TopM)
open import OCF.Align.UniformNFBase using (rΩ̂)

GR₂ : GR (Ω̂A 0 P̂) (ΩΩ ∷ ΩΩ ∷ [])
GR₂ = proj₂ (GA0-Ω̂ (GA0-Ω̂ good∅ᴿ))

module Accept₂ {ℓ} (ev : Ev ℓ (Fl₁ ⊔ fk zero)) (z : zero <ᴵ ℓ) (G : Goodᴺ (toZ (Ω̂A 0 P̂ ev z))) where
  L₂ : Lab₀ (Ω̂A 0 P̂ ev z) t2
  L₂ = g0 GR₂ ev z t2-NF

  agree : forceᴺ _ G ≅ forceᴸ _ (proj₁ L₂)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (rΩ̂ rP̂ ev z ev z (≅ᴵ-refl zero))) G (ofL (proj₁ L₂))) (ofL-≅ (proj₁ L₂))

  label : Lab (forceᴺ _ G) t2
  label = Lab-≅ agree (proj₂ L₂)

  tree : forceᴺ _ G ≅ T2ᴸ
  tree = Lab-uniq label T2-label

module A₂ {ℓ} (ev : Ev ℓ (Fl₁ ⊔ fk zero)) (z : zero <ᴵ ℓ) = Accept₂ ev z (TopM.Gᴺ₂ᵁ ev z)
```
