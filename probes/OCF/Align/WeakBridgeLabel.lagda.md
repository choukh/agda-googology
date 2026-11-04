# `T₀ʷ` 上的字面标签 (主审写的推论)

> 接 [WeakBridge](WeakBridge.lagda.md) 与 [OrdLab](OrdLab.lagda.md). `WeakBridge` 判断标签要再写约 400 行, 当时 `OrdLab` 还没回来. `OrdLab` 把标签贴到主线的 `LadderNFMain` 之后, 只要接一条链: `value-θ` (`T⁺ θ` 的计值 ≅ `HSℕ` 的证书的计值), `agree-ℕ` (`HSℕ` 的证书 ≅ `LadderNFMain`), `nf-main` (`LadderNFMain` 上的标签). **验收节, 读记号.** 这个文件不进证书.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeLabel where

open import Data.List using (_∷_; [])
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; Lab-≅)
import OCF.Align.EBO as E
open E using (T; Ωt; natT) renaming (_<ᵀ_ to _<ᵗ_)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; n[]; Ω₁; Ωᵐ)
open import OCF.Align.OrdLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabAccept using (nf-main)
open import OCF.Align.LadderInfAgree using (agree-ℕ)
open import OCF.Align.WeakBridgeMain using (Good-θ; value-θ; ev₀)

-- ψ₀(Ω_{Ω+θ}): 对任何带标签的可数 θ, 范围与 nf-main 相同
label-θ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ 0 [])) →
          ∀ {α} → α ≅ᴵ toLevel Y hY →
          Lab (forceᴺ _ (Good-θ α)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ 0 θ)))
label-θ Y hY lY nθ pm {α} e =
  Lab-≅ (value-θ α) (Lab-≅ (≅-sym (agree-ℕ 0 α _ zero)) (nf-main 0 Y hY lY nθ pm e _ zero))

-- 实例: θ = 0, 也就是 ψ₀(Ω_Ω). 说明前提可满足
label-Ω : Lab (forceᴺ _ (Good-θ zero)) (ψ₀ᵗ (Ωt (Ω₁ ∷ [])))
label-Ω = label-θ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅
  where open import Relation.Binary.PropositionalEquality using (refl)
```
