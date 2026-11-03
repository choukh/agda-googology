# 数据树上的无符号闭包定理 (十三): 验收

> 接 [UniformNF4Main](UniformNF4Main.lagda.md), [Uniform4Label](Uniform4Label.lagda.md). **记号只在本文.** `ofL`, `forceᴺ-≅` 把 `Uniform4Label` 的标签定理搬到记号无关的证书上: 证书的计值就是带标签的树. 构造不读这里的任何东西. 结论:
>
> 1. `label-Ω̇ c`: `GᴺΩ̇ c` 的计值带标签 $\psi_0(\Omega_{\Omega+c})$, 对一切 $c$. `label-Ω̇ 0` 是 $\psi_0(\Omega_\Omega)$, `label-Ω̇ 1` 是 $\psi_0(\Omega_{\Omega+1})$.
> 2. `label-Ω2 c`: $\psi_0(\Omega_{\Omega+c}\cdot2)$. `label-Ω+1 c`: $\psi_0(\Omega_{\Omega+c}+1)$. `label-sq`: $\psi_0(\Omega_\Omega^2)$. `label-Tω`: $\psi_0(\Omega_{\Omega+\omega})$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Accept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Align.Level
open import OCF.Align.Prefix using (toZ)
open import OCF.Align.UniformNF3Eq using (z≅; l≅; toZ-≅)
open import OCF.Align.Uniform3Base using (Ev; fz; fk; _⊔_; ψ₀ᵗ; fz∼)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.EBO using (Ωt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.Uniform4Head using (μ)
open import Data.List using ([]; _∷_; _++_)
open import OCF.Align.Uniform4Base
open import OCF.Align.UniformNF4Base using (RΩ̇; R→≈; R-⊕; R-ψ; R-ι; rs; rz)
open import OCF.Align.UniformNF4Main
import OCF.Align.Uniform4Label as U4
open import OCF.Align.Uniform3Base using (∼ᶠ-refl)

module AΩ̇ (c : ℕ) {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) where
  L = U4.TΩ-label c ev z

  agree : forceᴺ _ (GᴺΩ̇ c ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (RΩ̇ c) ev z ev z z≅)) (GᴺΩ̇ c ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-Ω̇ : Lab (forceᴺ _ (GᴺΩ̇ c ev z)) (ψ₀ᵗ (Ωt (μ c)))
  label-Ω̇ = Lab-≅ agree (proj₂ L)

module AΩ2 (c : ℕ) {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) where
  L = U4.TΩ·2-label c ev z

  agree : forceᴺ _ (GᴺΩ2 c ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (R-⊕ (∼ᶠ-refl Fl) (RΩ̇ c) (RΩ̇ c)) ev z ev z z≅)) (GᴺΩ2 c ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-Ω2 : Lab (forceᴺ _ (GᴺΩ2 c ev z)) (ψ₀ᵗ (Ωt (μ c) ++ Ωt (μ c)))
  label-Ω2 = Lab-≅ agree (proj₂ L)

module Asq {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) where
  L = U4.Tsq-label ev z

  agree : forceᴺ _ (Gᴺsq ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (R-ψ zero zero (R-ι zero (RΩ̇ 0))) ev z ev z z≅)) (Gᴺsq ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-sq : Lab (forceᴺ _ (Gᴺsq ev z)) tΩ2
  label-sq = Lab-≅ agree (proj₂ L)

module ATω {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) where
  L = U4.Tω-label ev z

  agree : forceᴺ _ (GᴺTω ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (l≅ (λ n → R→≈ (RΩ̇ n) ev z ev z z≅))) (GᴺTω ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-Tω : Lab (forceᴺ _ (GᴺTω ev z)) U4.tω
  label-Tω = Lab-≅ agree (proj₂ L)

module AΩ+1 (c : ℕ) {ℓ} (ev : Ev ℓ (Fl ⊔ fz)) (z : zero <ᴵ ℓ) where
  L = U4.TΩ+1-label c ev z

  agree : forceᴺ _ (GᴺΩ+1 c ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (R-⊕ (∼ᶠ-refl Fl) (RΩ̇ c) (rs fz∼ rz)) ev z ev z z≅)) (GᴺΩ+1 c ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-Ω+1 : Lab (forceᴺ _ (GᴺΩ+1 c ev z)) (ψ₀ᵗ (Ωt (μ c) ++ (𝟏 ∷ [])))
  label-Ω+1 = Lab-≅ agree (proj₂ L)
```
