# 阶梯 (七): $\psi_0(\Omega_{\Omega\cdot2+\theta})$ 的标签

> 结论写在 [ScafLadder](ScafLadder.lagda.md). `TΩ₂-label`: 对一切带标签的可数树 $Y$ (标签 $\theta$), $\psi_0(\Omega_{\Omega\cdot2+\theta})$. $\theta=0$ 是 $\psi_0(\Omega_{\Omega\cdot2})$, $\theta=1$ 是决定性的第一个目标, 没有按 $\theta$ 的抄写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.ScafLadderZStandardOmega using ()
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_; Ψ) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two renaming (ι to ιᵒ)
open import OCF.Align.ScafLadderZUniform5Class
open import OCF.Align.ScafLadderZUniform5Close
open import OCF.Align.ScafLadderZUniform5Tail
open import OCF.Align.ScafLadderZUniform5Tr
open import OCF.Align.ScafLadderZUniform5Psi
open import OCF.Align.ScafLadderZUniform5Rel hiding (R-ι; R-trˡ; R-tr⁻ˡ; R-resˡ; R-res⁻ˡ)
open import OCF.Align.ScafLadderZUniform5RelPsi hiding (R-trʳ; R-tr⁻ʳ; R-resʳ; R-res⁻ʳ)
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import Data.Empty using (⊥; ⊥-elim)
open import OCF.Align.ScafLadderTree
open import OCF.Align.ScafLadderClass
open import OCF.Align.ScafLadderPsi
open import OCF.Align.ScafLadderRel
open import OCF.Align.ScafLadderEval
open import OCF.Align.ScafLadderNF using (NF-Ωᵐ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.ScafLadderZStandardOmega using (NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <ᵀ-trans; cmpᵀ-refl; eq→≡; eq→≡ᴾ)
open import OCF.Align.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.ScafLadderZSystemOmega using (cmp-CΩ)
```

## §1 标准形

`NF-Ω₂` 是 [ScafLadderNF](ScafLadderNF.lagda.md) 的 `NF-Ωᵐ 1`. 这里 $\theta$ 要低于 $\psi_0(\Omega_{\Omega\cdot3})$, 否则这个项不是标准形.

```agda
Ωs₂ : T → T
Ωs₂ c = Ωt (μ (μ c))

B₃ : T
B₃ = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ []))

NF-Ω₂ : ∀ {θ} → NF₁ θ → Ctbl θ → θ <ᵗ B₃ → NF₁ (ψ₀ᵗ (Ωs₂ θ))
NF-Ω₂ = NF-Ωᵐ 1
```

## §2 主定理

```agda
TΩ₂-label : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B₃ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᴾ α ev p) (ψ₀ᵗ (Ωs₂ θ))
TΩ₂-label Y hY lY nθ pm e = labelᴾ (LpΩ̇ Y hY lY nθ e hon) (RΩ̇ᴾ (≅ᴵ-refl _)) ev₂ zero (NF-Ω₂ nθ (Lab→Ctbl lY nθ) pm)

-- ψ₀(Ω_{Ω·2+1})
t₂₁ : T
t₂₁ = ψ₀ᵗ (Ωs₂ (natT 1))

TΩ·2+1-label : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᴾ (suc zero) ev p) t₂₁
TΩ·2+1-label = TΩ₂-label one⁰ (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≅ z≅)

-- ψ₀(Ω_{Ω·2}) 在新树上
TΩ·2′-label : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᴾ zero ev p) (ψ₀ᵗ (Ωs₂ []))
TΩ·2′-label = TΩ₂-label Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅
```

## §3 对照与界

项是 [Uniform5Wall](Uniform5Wall.lagda.md) 的 `t₁`. **界与世界无关:** $\Omega_{\Omega\cdot2}$ 在目标 $t$ 之下落成字面闭包, 界在任何两个世界里 $\cong$, 所以路径上穿过的分支 $\tau$ 不进界. 这是 `noW` 的那个 $\tau$. `head-lit` 是 `refl`.

```agda
_ : t₂₁ ≡ ψ₀ᵗ (Ωt (sucT (Ωp ∷ Ωp ∷ [])))
_ = refl

head-lit : ∀ {t ℓ} (e : Ev ℓ Fl) (p : t <ᴵ ℓ) → Ψ {φ = Fl} e p (Ω̇ᴾ zero) ≡ oŝ (Bd (bound Fl e p)) _ _
head-lit e p = refl

bound-free : ∀ {t t′ ℓ ℓ′} (e : Ev ℓ Fl) (p : t <ᴵ ℓ) (e′ : Ev ℓ′ Fl) (p′ : t′ <ᴵ ℓ′) → t ≅ᴵ t′ → Bd (bound Fl e p) ≅ᴵ Bd (bound Fl e′ p′)
bound-free e p e′ p′ et = bound-≅ (⊔∼ fz∼ (fk∼ z≅)) e p e′ p′ et
```
