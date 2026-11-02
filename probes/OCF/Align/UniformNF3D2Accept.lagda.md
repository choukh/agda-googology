# 抽象类族上的折叠定理 (六): $\psi_0(\Omega_\Omega^2)$ 的验收

> 接 [UniformNF3D2T](UniformNF3D2T.lagda.md). **记号只在本文.** `Gᴺsq` 的构造不读这里的任何东西. `ofL` 与 `forceᴺ-≅` 把 [Uniform3Full](Uniform3Full.lagda.md) 的 `TΩ2-label` 搬到记号无关的证书上: 计值就是带标签 `tΩ2` 的树.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D2Accept where

open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Align.Level
open import OCF.Align.Prefix using (toZ)
open import OCF.Align.Uniform3Base using (Ev; fz; fk; _⊔_; Ω̂A; ∅ᴿ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.Uniform3Full using (TΩ2-label)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.UniformNF3D2T using (Gᴺsq; selfsq)

module Accept {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk zero))) (z : zero <ᴵ ℓ) where
  ev₀ : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))
  ev₀ = proj₁ ev , (proj₁ (proj₂ ev) , (proj₂ (proj₂ ev) , tt))

  L = TΩ2-label ev₀ z

  agree : forceᴺ _ (Gᴺsq ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (selfsq ev z) (Gᴺsq ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label-sq : Lab (forceᴺ _ (Gᴺsq ev z)) tΩ2
  label-sq = Lab-≅ agree (proj₂ L)
```
