# Uniform3 上的无符号闭包定理 (八): 验收

> 记号只在本文. `Gᴺk`、`Gᴺω` 的构造不读这里的任何东西. `forceᴺ-≅` 把 [Uniform3Base](Uniform3Base.lagda.md) 的标签搬到记号无关的计值树上, 再用 `Lab-uniq` 与 OmegaK 的 `Tkᴸ`、`Tωᴸ` 比较. 与 UniformPendingGoodTowerAccept 只差导入 (`good∅ᴿ` 取自 Uniform3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3TowerAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Align.Level
open import OCF.Align.Prefix using (toZ; Ordˢ)
open import OCF.Align.UniformS using (toZ-≅; _≅ˢ_)
open import OCF.Align.Uniform3Base using (Ev; GA0; GR; GA0-Ω̂; g0; Lab₀; ψ₀ᵗ)
open import OCF.Align.Uniform3 using (good∅ᴿ)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.EBO using (T)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.OmegaKBase using (ΠΩ; tk; tk-NF; tω)
open import OCF.Align.OmegaK using (Tkᴸ; Tk-label; Tωᴸ; Tω-label)
open import OCF.Align.UniformNF3NGrow using (PFl)
open import OCF.Align.UniformNF3Tower using (Fl; Pk; pfk; Gᴺk; Tkᵁ; Gᵁk; ev₁k; Tωᵁ; Gᴺω; G₃)

πk : ℕ → T
πk zero    = []
πk (suc k) = πk k ++ ΩΩ ∷ []

GA0k : ∀ k → GA0 (Pk k) (πk k)
GA0k zero    = good∅ᴿ
GA0k (suc k) = GA0-Ω̂ (GA0k k)

ΠΩ-snoc : ∀ n → ΠΩ n [] ++ ΩΩ ∷ [] ≡ ΩΩ ∷ ΠΩ n []
ΠΩ-snoc zero    = refl
ΠΩ-snoc (suc n) = cong (ΩΩ ∷_) (ΠΩ-snoc n)

π≡ : ∀ k → πk k ≡ ΠΩ k []
π≡ zero    = refl
π≡ (suc k) = trans (cong (_++ ΩΩ ∷ []) (π≡ k)) (ΠΩ-snoc k)

GRk : ∀ k → GR (Pk k) (ΠΩ k [])
GRk k = subst (GR (Pk k)) (π≡ k) (proj₂ (GA0k k))

module AcceptK (k : ℕ) {ℓ} (ev : Ev ℓ (Fl k)) (z : zero <ᴵ ℓ) (G : Goodᴺ (toZ (Pk k ev z))) where
  L : Lab₀ (Pk k ev z) (tk k)
  L = g0 (GRk k) ev z (tk-NF k)

  agree : forceᴺ _ G ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (forceᴺ-≅ (toZ-≅ (PFl.rP (pfk k) ev z ev z (≅ᴵ-refl zero))) G (ofL (proj₁ L))) (ofL-≅ (proj₁ L))

  label : Lab (forceᴺ _ G) (tk k)
  label = Lab-≅ agree (proj₂ L)

  tree : forceᴺ _ G ≅ Tkᴸ k
  tree = Lab-uniq label (Tk-label k)

tree-k : ∀ k → forceᴺ _ (Gᵁk k) ≅ Tkᴸ k
tree-k k = AcceptK.tree k (ev₁k k) zero (Gᵁk k)

label-k : ∀ k → Lab (forceᴺ _ (Gᵁk k)) (tk k)
label-k k = AcceptK.label k (ev₁k k) zero (Gᵁk k)

tree-3 : forceᴺ _ G₃ ≅ Tkᴸ 3
tree-3 = tree-k 3

tree-ω : forceᴺ _ Gᴺω ≅ Tωᴸ
tree-ω = l≅ tree-k

label-ω : Lab (forceᴺ _ Gᴺω) tω
label-ω = Lab-≅ tree-ω Tω-label
```
