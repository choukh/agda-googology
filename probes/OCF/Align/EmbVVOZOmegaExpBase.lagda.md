> **机械克隆, 验收用.** 由 `OrdLabZOmegaExpBase` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZOmegaExpBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ; ++-assoc) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZSymbolic using (Mlev; σ1)
open import OCF.Align.EmbVVOZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.OrdLabZBachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.OrdLabZClosure using (Pen; fsT₊-pen′; lt→<)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (Desc; d₀; Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.EmbVVLZExtra using (occ<)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.EmbVVOZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.EmbVVOZGoodLBase
open import OCF.Free.Aux public using (σ⊥)
open import OCF.Align.LadderLabZOmegaExpBase public using (++-ne; 1<γ; 1<ψ; H1W; OccΣ; cofW; cofΣ; fsT-ne; fsT0-ne; fsTc-ne; fsTΣ; fsT₊-ne; fsnΣ; gtW; onCons; penW; predΣ; repW; γW; γW-eq; γW-ne; πw; ωW)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
```

## §4 一般栈上的带前缀 $\psi_w$, 目标 $w\ne0$

```agda
ne-w : ∀ {i w} → (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → w ≡ [] → ⊥
ne-w Iw ei ki refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
```

## §8 结论与边界
