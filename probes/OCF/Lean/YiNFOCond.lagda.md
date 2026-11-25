# 记号参照: 一切可数标准形上的项序推出值序 (条件)

> 验收文件 (读记号). 条件定理, 条件是一条: `CofinNF` (可数 EBO 标准形 `EboLeanBase.NF` 上 ω-基本列共尾). 在此条件下, [YiNFO](YiNFO.lagda.md) 的 `mono<` 推广到一切可数标准形 (`mono<ᶜ`), 于是 `YiRefTw2` 的 `Row₂` 推出 `Step₂⁺` (`row₂→step⁺`).
> 证明与 `mono<` 逐行相同, 只把 `cofin₁`, `NF₁-fsn`, `NF₁-pred` 换成条件、`cl-fsn-NF`、`nf-pred`. `CofinNF` 未证; 它在 `NF₁` 上的对应是 `StandardOmega.cofin₁`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNFOCond where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω; fsn; EBOψ; _<ᵀ_; []<; hd<; lv<; ar<)
open import OCF.Align.EboLeanBase using (NF; nf-pred; Ctbl; c[]; c∷; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; Ctbl-fsn)
open import OCF.Align.EboLeanTree using (hc-tower; nf-tower)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼; t₊; nf₊; h₊; Row₂; Step₂⁺)
open import OCF.Lean.YiNFO using (c0-min; pred-≤; ↓suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-trans)
```

```agda
CofinNF : Set
CofinNF = ∀ {s t} → NF t → Ctbl t → cof t ≡ cω → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fsn t n

mono<ᶜ : CofinNF → ∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → s <ᵀ t →
         L.suc (Rt h) ≼ Rt h′
mono<ᶜ C ns nt ct h (h0 e) p = ⊥-elim (c0-min e p)
mono<ᶜ C ns nt ct h (h1 e hp) p with pred-≤ e p
... | inj₁ q = s≼s (↓suc (mono<ᶜ C ns (nf-pred nt) (Ctbl-pred ct) h hp q))
... | inj₂ r = s≼s (tree-≼ r h hp)
mono<ᶜ C ns nt ct h (hω e hs) p with C nt ct e ns p
... | n , q = ≼l n (mono<ᶜ C ns (cl-fsn-NF nt e n) (Ctbl-fsn ct e n) h (hs n) q)

mono≤ᶜ : CofinNF → ∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → (s <ᵀ t) ⊎ (s ≡ t) →
         Rt h ≼ Rt h′
mono≤ᶜ C ns nt ct h h′ (inj₁ p) = ↓suc (mono<ᶜ C ns nt ct h h′ p)
mono≤ᶜ C ns nt ct h h′ (inj₂ r) = tree-≼ r h h′
```

塔的一行之下的可数标准形, 参照严格低于那一行的参照; 实例: ψ₀(Ω_{Ω+1}) 低于 ψ₀(Ω_{Ω_Ω}).

```agda
below-row : CofinNF → ∀ k {s} → NF s → (h : HC s) → s <ᵀ EBOψ k → L.suc (Rt h) ≼ Rt (hc-tower k)
below-row C k ns h p = mono<ᶜ C ns (nf-tower k) (c∷ c[]) h (hc-tower k) p

t₊<row3 : t₊ <ᵀ EBOψ 3
t₊<row3 = hd< (ar< (hd< (lv< (hd< (lv< (hd< (lv< []<)))))))

row₂→step⁺ : CofinNF → Row₂ → Step₂⁺
row₂→step⁺ C r = ≼-trans (↓suc (below-row C 3 nf₊ h₊ t₊<row3)) r
```
