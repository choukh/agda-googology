# 一切深度 (十): 验收

> 接 [UniformNF3D3Z](UniformNF3D3Z.lagda.md). **记号只在本文.** 证书的构造不读这里的任何东西. `ofL` 与 `forceᴺ-≅` 把 [Uniform3OmegaPlus1](Uniform3OmegaPlus1.lagda.md) 的标签定理搬到记号无关的证书上. 结论先说:
>
> 1. **`AΨ.label`: $\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))$ 的证书的计值带标签 `ψ₀ᵗ (γΩ [] 2)`.** 决定性检验通过.
> 2. **`APt.label n`: 替身第 $n$ 点的证书的计值带标签 `ψ₀ᵗ (γΩ [] n)`, 对一切 $n$.**
> 3. **`AO.label`: $\psi_0(\Omega_{\Omega+1})$ 的证书的计值带标签 `tO`.** §2 的 `corΓ′` 把 D3B 抄的树 `OP` 与那边的 `OmegaPlus ∅ᵀ` 用互模拟连起来.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3Accept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ordˢ; toZ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans; _≅ˢ_; ≅ˢ-sym; ≅ˢ-trans; toZ-≅; l≅; _≈ᴿ_)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ; fz; fk; _⊔_; Ev; Run; wk; Ω̂A; ∅ᴿ; Ψ; ∅ᵀ; ψᵀ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.UniformNF3D3W using (er)
open import OCF.Align.UniformNF3D3T using (ws)
open import OCF.Align.UniformNF3D3B using (T′; module OP; plus; pt≈; capp; CA; CorS; ≃-refl; ≃-unitr; CΘf; wkS; cw; csw)
open import OCF.Align.UniformNF3D3Z using (Gᴺ-Ψ3; self-Ψ3; Gᴺ-Ω⁺; evT; Gz; pt; Gpt)
open import OCF.Align.Uniform3OmegaPlus1 using (TΨ³-label; TO-label; module OmegaPlus; module Pts)
open import OCF.Align.OmegaPlus1Base using (γΩ)
open import OCF.Align.Stage2 using (tO)
```

## §1 决定性检验

```agda
module AΨ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ (fk zero ⊔ fz))))) (z : zero <ᴵ ℓ) where
  L = TΨ³-label ev z

  agree : forceᴺ _ (Gᴺ-Ψ3 ev z) ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (self-Ψ3 ev z) (Gᴺ-Ψ3 ev z) (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label : Lab (forceᴺ _ (Gᴺ-Ψ3 ev z)) (ψ₀ᵗ (γΩ [] 2))
  label = Lab-≅ agree (proj₂ L)
```

## §2 替身: 与带标签文件的树连起来

```agda
module O′ = OmegaPlus ∅ᵀ

corΓ′ : ∀ n m (c : CA (suc m)) → CorS c (er (ws m)) → capp c (O′.ΓS n m) ≈ᴿ T′ (plus n m)
corΓ′ zero m (fl , P , c) (sφ , cP , cs) =
  wkS c (wkS c (CΘf m {fl ⊔ fz , wk m proj₁ P , c} {er (ws m)} (≃-unitr sφ , (λ {c′} cs′ → wkS c′ (cP cs′)) , cs)))
corΓ′ (suc n) m (fl , P , c) (sφ , cP , cs) =
  wkS c (corΓ′ n (suc m) (fk zero , Ω̂A m , fl ⊔ fz , wk m proj₁ P , c)
    (≃-refl (fk zero) , CΘf m , ≃-unitr sφ , (λ {c′} cs′ → wkS c′ (cP cs′)) , cs))

pt′ : ∀ n {ℓ} → Ev ℓ (fz ⊔ (fz ⊔ fk zero)) → zero <ᴵ ℓ → Ordˢ zero
pt′ n ev z = Pts.pt n ev z

d-pt : ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) → pt n ev z ≅ˢ pt′ n ev z
d-pt n ev z = ≅ˢ-trans (pt≈ n (OP.leΓ n ev) z (evT (plus n 0) z) z (≅ᴵ-refl zero))
                       (≅ˢ-sym (corΓ′ n 0 (cw 0) (csw 0) (O′.leΓ n ev) z (evT (plus n 0) z) z (≅ᴵ-refl zero)))

module APt (n : ℕ) {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) where
  G : Goodᴺ (toZ (pt′ n ev z))
  G = Goodᴺ-tr (toZ-≅ (d-pt n ev z)) (Gpt n ev z)

  L = Pts.TO-pt n ev z

  self′ : toZ (pt′ n ev z) ≅ᶻ toZ (pt′ n ev z)
  self′ = toZ-≅ (≅ˢ-trans (≅ˢ-sym (d-pt n ev z)) (d-pt n ev z))

  agree : forceᴺ _ G ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ self′ G (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label : Lab (forceᴺ _ G) (ψ₀ᵗ (γΩ [] n))
  label = Lab-≅ agree (proj₂ L)

module AO {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) where
  e : ψᵀ OP.Ω⁺ ev z ≅ˢ ψᵀ O′.Ω⁺ ev z
  e = l≅ (λ n → d-pt n ev z)

  G : Goodᴺ (toZ (ψᵀ O′.Ω⁺ ev z))
  G = Goodᴺ-tr (toZ-≅ e) (Gᴺ-Ω⁺ ev z)

  L = TO-label ev z

  self′ : toZ (ψᵀ O′.Ω⁺ ev z) ≅ᶻ toZ (ψᵀ O′.Ω⁺ ev z)
  self′ = toZ-≅ (≅ˢ-trans (≅ˢ-sym e) e)

  agree : forceᴺ _ G ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ self′ G (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label : Lab (forceᴺ _ G) tO
  label = Lab-≅ agree (proj₂ L)
```
