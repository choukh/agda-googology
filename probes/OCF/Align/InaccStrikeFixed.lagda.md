# `T₂-cert→⊥` 的更正

> [InaccStrike](InaccStrike.lagda.md) §2 的 `T₂-cert→⊥` 第四个前提对一切 `b` 要原像, 取常值 `zero` 就矛盾, 所以那条定理是空真 (`H-vacuous`). 这里是不空的版本: 前提只对判决 `D zero i₀` 实际返回的 `pen r′ b` 要原像 (`Fixed.T₂-cert→⊥′`), 证明不变. 来自 2026-11-03 的 Fable 5.1 独立审核. 老文件不改, 以这里为准. 这条否定在路线上的分量见 `probes/LOG.md`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification --guardedness #-}
module OCF.Align.InaccStrikeFixed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccTree
open import OCF.Align.InaccStrike using (i₀; no-sound)


-- 审核: InaccStrike.T₂-cert→⊥ 的第四个前提 H 对任何 G 都自相矛盾
-- (取 b = 常值 zero, 则 b y ≡ suc ω⁺T 不可能), 所以该定理是空真.
H-vacuous : (G : ∀ {k} → Ordᴸ k → Set) →
  (∀ (r′ : Pre i₀) (b : Ordᴸ (at i₀ r′) → Ordᴸ zero) →
     Σ (Ordᴸ (at i₀ r′)) λ y → (b y ≡ suc ω⁺T) × G y) → ⊥
H-vacuous G H with H (inj₁ tt) (λ _ → zero)
... | y , () , _

module Fixed (D : Oracle) (G : ∀ {k} → Ordᴸ k → Set) where
  open Cert D G
  open Terms D using (Ω̂)
  open OCF.Align.InaccStrike.Forced D G using (x₂; rc-only; rise₀; sound-at)

  pen-only′ : ∀ {k r f} → at k r ≡ zero → Run i₀ k (limᵢ r f) →
              Σ (Pre i₀) λ r′ → Σ (Ordᴸ (at i₀ r′) → Ordᴸ (at k r)) λ b →
              (D (at k r) i₀ ≡ pen r′ b) × (∀ y → G y → Run i₀ k (f (intoL k r (b y))))
  pen-only′ z (rp {r′ = r′} {b = b} e s h) = r′ , b , e , h
  pen-only′ {k} {r} z (rc e s g₀ h₁ h₂ h₃) = ⊥-elim (bad (at k r) z (subst Sound e s)) where
    bad : ∀ ℓ → ℓ ≡ zero → (i₀ ≺ ℓ ⊎ i₀ ≅ ℓ) → ⊥
    bad _ refl (inj₁ (via () _))
    bad _ refl (inj₂ ())

  T₂-cert→⊥′ : Run zero L₁ (Ω̂ + Ω̂) → G x₂ → G {i₀} zero →
               (∀ (r′ : Pre i₀) (b : Ordᴸ (at i₀ r′) → Ordᴸ zero) → D zero i₀ ≡ pen r′ b →
                  Σ (Ordᴸ (at i₀ r′)) λ y → (b y ≡ suc ω⁺T) × G y) → ⊥
  T₂-cert→⊥′ run g₂ g₀ H with pen-only′ {L₁} {inj₁ (inj₁ tt)} refl (rc-only (rise₀ run x₂ g₂) zero g₀)
  ... | r′ , b , e , h with H r′ b e
  ...   | y , q , gy = no-sound D (sound-at (unup (subst (λ z → Run i₀ L₁ (up z (Ω (toLv z)))) q (h y gy)))) where
    unup : Run i₀ L₁ (up (suc ω⁺T) (Ω (toLv (suc ω⁺T)))) → Run i₀ (toLv (suc ω⁺T)) (Ω (toLv (suc ω⁺T)))
    unup (ru q′) = q′
```
