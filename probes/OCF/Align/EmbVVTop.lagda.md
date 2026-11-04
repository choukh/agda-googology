# 值验收 (参照树): 去头的树带字面标签, 主线的树与它同值

> 入口 [EmbVV](EmbVV.lagda.md). 读记号. 对一切 `HtB`, 开关 `dr`, 前缀结构 `PxB 𝕊 dr`. `label-tree`: 去头的树带字面标签, 证书由标签类给 (`Goodᴸ`), 没有 `Goodᴺ` 闭包定理. `vv-row`: 主线的第 $\alpha$ 行过值验收, 只要层号 $\alpha\simeq$ `toLevel Y`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
open import OCF.Align.EmbVVBBase
import OCF.Align.EmbVVMode
module OCF.Align.EmbVVTop (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) (𝕏 : PxB 𝕊 dr) where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.OrdLabZLevel
import OCF.Align.EBO as E
open E using (T; Ωt)
open import OCF.Align.OrdLabZCorrespond using (Lab; Lab-≅)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁)
open import OCF.Align.EmbVVOZUniform3Base using (Ev; Lab₀; ψ₀ᵗ)
open import OCF.Align.EmbVVOZUniform4Base using (Fl)
open import OCF.Align.EmbVVOZUniform5Class using (hon)
open import OCF.Align.EmbVVOZGoodLBase using (forceᴸ)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.EmbVVForget using (ofL; ofL-≅)
open import OCF.Align.EmbVVTree 𝕊 dr
open import OCF.Align.EmbVVBClass 𝕊 dr 𝕏 using (LqΩ̇)
open import OCF.Align.EmbVVBRel 𝕊 dr 𝕏 using (RΩ̇)
open import OCF.Align.EmbVVBEval 𝕊 dr 𝕏 using (labelᵠ)
open import OCF.Align.EmbVVEq using (_≃ᴵ_)
open import OCF.Align.EmbVVMain 𝕊 using (module WithY; ≈-≅ʳ)
open import OCF.Align.ValLabLadder 𝕊 using (V; ev₀)
open import OCF.Align.ValLabPos using (VV)
open PxB 𝕏
open WithY dr using (Y-val)

label-tree : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψ₀ᵗ (Ωt (P m θ))) → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ m α ev p) (ψ₀ᵗ (Ωt (P m θ)))
label-tree m Y hY lY nθ nf e = labelᵠ (LqΩ̇ m Y hY lY nθ e hon) (RΩ̇ m (≅ᴵ-refl _)) ok₀ (λ i h r → ok₀ i) nf

vv-row : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψ₀ᵗ (Ωt (P m θ))) → ∀ {α} → α ≃ᴵ toLevel Y hY → VV (V m α) (ψ₀ᵗ (Ωt (P m θ)))
vv-row m Y hY lY nθ nf {α} d = forceᴸ _ (proj₁ L) , proj₂ L , proj₁ E₁ , proj₂ E₁
  where
  L = label-tree m Y hY lY nθ nf (≅ᴵ-refl (toLevel Y hY)) ev₀ zero
  E₁ = ≈-≅ʳ (Y-val m d (ofL (proj₁ L))) (≅-sym (ofL-≅ (proj₁ L)))
```
