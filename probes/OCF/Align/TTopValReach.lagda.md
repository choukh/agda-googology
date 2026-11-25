# `T⊤` 的值 (二): 现有标签工具够不到参照树的第 $n\ge1$ 项

> 验收文件, 读记号. **定理, 无条件:** `reachᴱ`, `reachᴸ`: 两版 `NF₁` (`vv-row` 与 `label-tree`, `ord-*` 的前提) 里, $\psi_0(\Omega_{\psi_1(a)+\cdots})$ 只容 $a\in\{0,1\}$; 所以 `no-NF-br`: 参照树 $\psi_0(\Omega_{\Omega^2})$ 的第 $n+1$ 项 $\psi_0(\Omega_{\psi_1(\gamma_{n+1})})$ 两版都不是 `NF₁`.
> 不否定: 这些项的值验收, 也不否定别的工具; 只说 `vv-row` 一族的前提给不出来. 入口 [TTopVal](TTopVal.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TTopValReach where

open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EBO using (T; ψ; natT; Ωt; fsn)
open import OCF.Align.LadderLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.CrossMAccept using (tψΩ; fs-ψΩ)
import OCF.Align.EmbVVLZStandardOmega as Eᵛ
import OCF.Align.LadderLabZStandardOmega as Lᵛ

sbᴱ : ∀ {a xs} → Eᵛ.Sb (ψ (natT 1) a ∷ xs) → (a ≡ natT 1) ⊎ (a ≡ [])
sbᴱ (Eᵛ.sψ⁺ k n c) = inj₁ refl
sbᴱ (Eᵛ.sψ n c) = inj₁ refl
sbᴱ (Eᵛ.sC ())
sbᴱ (Eᵛ.sΩ c) = inj₂ refl
sbᴱ (Eᵛ.sΩ² n c) = inj₂ refl

reachᴱ : ∀ {a xs} → Eᵛ.NF₁ (ψ₀ᵗ (Ωt (ψ (natT 1) a ∷ xs))) → (a ≡ natT 1) ⊎ (a ≡ [])
reachᴱ (Eᵛ.n∷ (Eᵛ.nψ _ _ (Eᵛ.n∷ (Eᵛ.nψ _ s _ _) _ _) _) _ _) = sbᴱ s

sbᴸ : ∀ {a xs} → Lᵛ.Sb (ψ (natT 1) a ∷ xs) → (a ≡ natT 1) ⊎ (a ≡ [])
sbᴸ (Lᵛ.sψ n c) = inj₁ refl
sbᴸ (Lᵛ.sC ())
sbᴸ (Lᵛ.sΩ c) = inj₂ refl
sbᴸ (Lᵛ.sΩ² n c) = inj₂ refl

reachᴸ : ∀ {a xs} → Lᵛ.NF₁ (ψ₀ᵗ (Ωt (ψ (natT 1) a ∷ xs))) → (a ≡ natT 1) ⊎ (a ≡ [])
reachᴸ (Lᵛ.n∷ (Lᵛ.nψ _ _ (Lᵛ.n∷ (Lᵛ.nψ _ s _ _) _ _) _) _ _) = sbᴸ s

no-NF-brᴱ : ∀ n → Eᵛ.NF₁ (fsn tψΩ (suc n)) → ⊥
no-NF-brᴱ n h with reachᴱ (subst Eᵛ.NF₁ (fs-ψΩ (suc n)) h)
... | inj₁ ()
... | inj₂ ()

no-NF-brᴸ : ∀ n → Lᵛ.NF₁ (fsn tψΩ (suc n)) → ⊥
no-NF-brᴸ n h with reachᴸ (subst Lᵛ.NF₁ (fs-ψΩ (suc n)) h)
... | inj₁ ()
... | inj₂ ()
```
