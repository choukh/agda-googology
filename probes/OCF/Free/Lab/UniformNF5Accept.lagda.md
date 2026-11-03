# UniformNF5Accept (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [UniformNF5Accept](../../Align/UniformNF5Accept.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.UniformNF5Accept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅)
open import OCF.Free.Lab.Uniform3Base using (Ev; fk; _⊔_; ψ₀ᵗ)
open import OCF.Free.Lab.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Free.Lab.Correspond using (Lab; Lab-≅)
open import OCF.Free.Lab.GoodLBase using (forceᴸ)
open import OCF.Free.Lab.StandardOmega using (NF₁)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Tree
open import OCF.Free.Lab.Uniform4TwoWalk using (tΩ·2)
open import OCF.Free.Lab.Uniform5Label using (TΩ-label; Ωs₊)
open import OCF.Free.Lab.Uniform5Top using (TΩ·2-label)
open import OCF.Free.Base using (RΩ̇; R→≈)
open import OCF.Free.Main 
```

```agda
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
