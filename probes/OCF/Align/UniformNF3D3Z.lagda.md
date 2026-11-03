# 一切深度 (九): 证书

> 接 [UniformNF3D3B](UniformNF3D3B.lagda.md). 结论先说:
>
> 1. **`Gᴺ-Ψ3`: $\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))$ 的记号无关证书.** 树用到 `Ω̂A 2`. 这是决定性检验.
> 2. **`Gᴺ-Ω̂ n`: `Ω̂A n (Ω̂A (n-1)) … (Ω̂A 0) ∅ᴿ` 的证书, 对一切 $n$, 同一个定理.**
> 3. **`Gᴺ-Ω⁺`: $\psi_0(\Omega_{\Omega+1})$ 的证书.** 树是 `lim n. ΓS n`; 单调性直接来自闭包算子的 `stE`: `T (n+1)` 的头就是 `T n`, $\Theta\,s\sqsupseteq$ 头 $+1$. 验收在 [UniformNF3D3Accept](UniformNF3D3Accept.lagda.md).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3Z where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans; _≅ˢ_; ≅ˢ-sym; ≅ˢ-trans; toZ-≅; l≅; _≈ᴿ_)
open import OCF.Align.Uniform3Base using (fz; fk; _⊔_; Ev; Run; Ω̂A; ∅ᴿ; Ψ; ∅ᵀ; ψᵀ)
open import OCF.Align.NotFree using (Goodᴺ; gl; forceᴺ; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (sf)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.UniformNF3D3G using (_⊑ᴱ_; FFl; suc-rᴱ; ≅→⊑ᴱ; ⊑ᴱ-trans; FlU≈; SF≈)
open import OCF.Align.UniformNF3D3S using (τ)
open import OCF.Align.UniformNF3D3W using (er; fX; sfW)
open import OCF.Align.UniformNF3D3T using (ws; Θf; RFΘf; T; GΘ)
open import OCF.Align.UniformNF3D3B using (T′; module OP; plus; plus-suc; pt≈; Ψ3≈; capp; cw; csw; CΘf)
open OP
```

## §1 塔的第 $j$ 层

```agda
evW : ∀ j {ℓ} → zero <ᴵ ℓ → Ev ℓ (sf (er (ws j)))
evW zero    z = tt , tt
evW (suc j) z = evW j z , τ z

evT : ∀ j {ℓ} → zero <ᴵ ℓ → Ev ℓ (sf (er (ws j)) ⊔ fk zero)
evT j z = evW j z , τ z

Tz : ∀ j {ℓ} → zero <ᴵ ℓ → Ordˢ zero
Tz j z = T′ j (evT j z) z

Gz : ∀ j {ℓ} (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tz j z))
Gz j z = GΘ j (evT j z) z

selfT : ∀ j {ℓ} {i} {ev : Ev ℓ (sf (er (ws j)) ⊔ fk zero)} (p : i <ᴵ ℓ) → T′ j ev p ≅ˢ T′ j ev p
selfT j {ev = ev} p = FlU≈ (suc j) (fX (RFΘf j)) (SF≈ (sfW (ws j))) ev p ev p (≅ᴵ-refl _)

leT : ∀ j {ℓ} (z : zero <ᴵ ℓ) → Tz j z ⊑ᴱ Tz (suc j) z
leT j z = ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (selfT j z))) (FFl.stE (fX (RFΘf (suc j))) (sfW (ws (suc j))) (evT (suc j) z) z)

monoT : ∀ j {ℓ} (z : zero <ᴵ ℓ) → forceᴺ _ (Gz j z) ⊑ forceᴺ _ (Gz (suc j) z)
monoT j z = ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (selfT j z)) (Gz j z) (proj₁ L))) (proj₂ L)
  where L = leT j z OCF.Align.UniformNF3D3O.idO (Gz (suc j) z)
```

## §2 证书

```agda
Gᴺ-Ω̂ : ∀ n {ℓ} (ev : Ev ℓ (sf (er (ws n)) ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (T′ n ev z))
Gᴺ-Ω̂ n ev z = GΘ n ev z

Gᴺ-Ω̂ᶜ : ∀ n {ℓ} ev (z : zero <ᴵ ℓ) → Goodᴺ (toZ (capp (cw n) (Ω̂A n) ev z))
Gᴺ-Ω̂ᶜ n ev z = Goodᴺ-tr (≅ᶻ-sym (toZ-≅ (CΘf n (csw n) ev z (evT n z) z (≅ᴵ-refl zero)))) (Gz n z)

Gᴺ-Ψ3 : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψᵀ (Ψ (Ψ (Ψ ∅ᵀ))) ev z))
Gᴺ-Ψ3 ev z = Goodᴺ-tr (≅ᶻ-sym (toZ-≅ (Ψ3≈ ev z (evT 2 z) z (≅ᴵ-refl zero)))) (Gz 2 z)

self-Ψ3 : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → toZ (ψᵀ (Ψ (Ψ (Ψ ∅ᵀ))) ev z) ≅ᶻ toZ (ψᵀ (Ψ (Ψ (Ψ ∅ᵀ))) ev z)
self-Ψ3 ev z = toZ-≅ (≅ˢ-trans (Ψ3≈ ev z (evT 2 z) z (≅ᴵ-refl zero)) (≅ˢ-sym (Ψ3≈ ev z (evT 2 z) z (≅ᴵ-refl zero))))

pt : ∀ n {ℓ} → Ev ℓ (fz ⊔ (fz ⊔ fk zero)) → zero <ᴵ ℓ → Ordˢ zero
pt n ev z = ΓS n 0 ∅ᴿ (leΓ n ev) z

dpt : ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) → toZ (Tz (plus n 0) z) ≅ᶻ toZ (pt n ev z)
dpt n ev z = ≅ᶻ-sym (toZ-≅ (pt≈ n (leΓ n ev) z (evT (plus n 0) z) z (≅ᴵ-refl zero)))

Gpt : ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (pt n ev z))
Gpt n ev z = Goodᴺ-tr (dpt n ev z) (Gz (plus n 0) z)

fpt : ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) → forceᴺ _ (Gz (plus n 0) z) ≅ forceᴺ _ (Gpt n ev z)
fpt n ev z = forceᴺ-≅ (dpt n ev z) (Gz (plus n 0) z) (Gpt n ev z)

mono-idx : ∀ j j′ {ℓ} (z : zero <ᴵ ℓ) → j′ ≡ suc j → forceᴺ _ (Gz j z) ⊑ forceᴺ _ (Gz j′ z)
mono-idx j j′ z e = subst (λ k → forceᴺ _ (Gz j z) ⊑ forceᴺ _ (Gz k z)) (sym e) (monoT j z)

Gᴺ-Ω⁺ : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fz ⊔ fk zero))) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψᵀ Ω⁺ ev z))
Gᴺ-Ω⁺ ev z = gl (λ n → Gpt n ev z)
  (λ n → ⊑-trans (≅→⊑ (≅-sym (fpt n ev z)))
          (⊑-trans (mono-idx (plus n 0) (plus (suc n) 0) z (plus-suc n 0))
                   (≅→⊑ (fpt (suc n) ev z))))
```
