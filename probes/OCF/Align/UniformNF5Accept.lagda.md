# 层号参数化的无符号闭包定理 (十三): 验收

> 接 [UniformNF5Main](UniformNF5Main.lagda.md), [Uniform5Label](Uniform5Label.lagda.md), [Uniform5Top](Uniform5Top.lagda.md). **记号只在本文.** `ofL`, `forceᴺ-≅` 把标签定理搬到记号无关的证书上: 证书的计值就是带标签的树. 构造不读这里的任何东西. 结论:
>
> 1. `label-Ω̇ Y hY lY nθ e`: 只要 $\alpha\cong$ `toLevel Y hY`, $Y$ 带标签 $\theta\in$ `NF₁`, `GᴺΩ̇ α` 的计值带标签 $\psi_0(\Omega_{\Omega+\theta})$. 证书 `GᴺΩ̇ α` 本身不要这些前提: 它对一切 $\alpha$ 成立; 前提只是标签定理的前提.
> 2. `label-TΩ·2`: `GᴺTΩ·2` 的计值带标签 $\psi_0(\Omega_{\Omega\cdot2})$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Accept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Align.Level
open import OCF.Align.Prefix using (toZ)
open import OCF.Align.UniformNF3Eq using (z≅; toZ-≅)
open import OCF.Align.Uniform3Base using (Ev; fk; _⊔_; ψ₀ᵗ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.StandardOmega using (NF₁)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two
open import OCF.Align.Uniform4TwoWalk using (tΩ·2)
open import OCF.Align.Uniform5Label using (TΩ-label; Ωs₊)
open import OCF.Align.Uniform5Top using (TΩ·2-label)
open import OCF.Align.UniformNF5Base using (RΩ̇; R→≈)
open import OCF.Align.UniformNF5Main

module AΩ̇ {θ} (Y : Ordᶜ zero) (hY : HS Y) (lY : Lab Y θ) (nθ : NF₁ θ) {α} (e : α ≅ᴵ toLevel Y hY) {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) where
  L = TΩ-label Y hY lY nθ e ev z

  agree : forceᴺ _ (GᴺΩ̇ α ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (RΩ̇ (≅ᴵ-refl α)) ev z ev z z≅)) (GᴺΩ̇ α ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-Ω̇ : Lab (forceᴺ _ (GᴺΩ̇ α ev z)) (ψ₀ᵗ (Ωs₊ θ))
  label-Ω̇ = Lab-≅ agree (proj₂ L)

module ATΩ·2 {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (z : zero <ᴵ ℓ) where
  L = TΩ·2-label ev z

  agree : forceᴺ _ (GᴺTΩ·2 ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (RTΩ·2 ev z ev z z≅)) (GᴺTΩ·2 ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-TΩ·2 : Lab (forceᴺ _ (GᴺTΩ·2 ev z)) tΩ·2
  label-TΩ·2 = Lab-≅ agree (proj₂ L)
```
