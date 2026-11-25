# 记号参照: 一切可数标准形上项序推出值序 (无前提)

> 验收文件 (读记号, 不进成品). 判决: `YiNFOCond.CofinNF` 是定理 (`cofinNF`, 由 [YiCFCofin](YiCFCofin.lagda.md) 的 `cofin` 去掉不用的 `Ctbl` 前提), 于是 `YiNFOCond` 的条件定理都无前提成立: `mono<ⁿ`, `mono≤ⁿ`, `below-rowⁿ`, `row₂→step⁺ⁿ`.
> 不否定什么, 不涉及上界; `Row₂` 本身仍未证, `row₂→step⁺ⁿ` 只是蕴涵.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCFMono where

open import Data.Sum using (_⊎_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.EboLeanDef using (HC; EBOψ; _<ᵀ_)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.EboLeanTree using (hc-tower; nf-tower)
open import OCF.Lean.YiRefTw2 using (Rt; Row₂; Step₂⁺; nf₊)
open import OCF.Lean.YiNFOCond using (CofinNF; mono<ᶜ; mono≤ᶜ; below-row; row₂→step⁺; t₊<row3)
open import OCF.Lean.YiCFCofin using (cofin)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
```

```agda
cofinNF : CofinNF
cofinNF nt _ e ns p = cofin nt e ns p

mono<ⁿ : ∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → s <ᵀ t →
         L.suc (Rt h) ≼ Rt h′
mono<ⁿ = mono<ᶜ cofinNF

mono≤ⁿ : ∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → (s <ᵀ t) ⊎ (s ≡ t) →
         Rt h ≼ Rt h′
mono≤ⁿ = mono≤ᶜ cofinNF

below-rowⁿ : ∀ k {s} → NF s → (h : HC s) → s <ᵀ EBOψ k → L.suc (Rt h) ≼ Rt (hc-tower k)
below-rowⁿ = below-row cofinNF

row₂→step⁺ⁿ : Row₂ → Step₂⁺
row₂→step⁺ⁿ = row₂→step⁺ cofinNF
```

有限测试 (不是定理的一部分): ψ₀(Ω_{Ω+1}) 低于第 3 行 ψ₀(Ω_{Ω_Ω}) 的第 1 项 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}), `refl` 算出.

```agda
_ : proj₁ (cofin (nf-tower 3) refl nf₊ t₊<row3) ≡ 1
_ = refl
```
