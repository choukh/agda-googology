# Uniform3Depth1 (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform3Depth1](LadderLabZUniform3Depth1.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform3Depth1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZSymbolic using (Mlev; Fs; Fst)
open import OCF.Align.OrdLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ; H1-pen; H1-fsT)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.OrdLabZBachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.OrdLabZClosure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP; Lab0[])
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZOmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq; gtW; penW; H1W; ne-w; 1<γ; ++-ne; fsT-ne)
open import OCF.Align.OrdLabZOmegaSqBase using (cmpΩ)
open import OCF.Align.OrdLabZUniform3Base
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              []<; cofA) renaming (ψ to ψᵗ)
```

## §11 深度 1 的折叠定理 (地板平凡的尾巴)

```agda
wkL0 : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → L0 R u → L0 (wk 0 le R) u
wkL0 le h ev p = h (le ev) p

module _ (ζ : T) {y : PT} {ys : T} where
  cωΩ : cof (y ∷ ys) ≡ cω → cof (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) ≡ cω
  cωΩ c = trans (cofW Ωᵗ ζ y ys) (cong (cofA Ωᵗ) c)
  cΩΩ : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Idx ν → cof (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) ≡ cΩ ν
  cΩΩ {ν} c I = trans (cofW Ωᵗ ζ y ys) (trans (cong (cofA Ωᵗ) c) (cofP {w = Ωᵗ} {ν = ν} (inj₁ (cmpΩ I))))
  penΩ : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Idx ν → ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ fsT (y ∷ ys) η) ∷ []
  penΩ {ν} c I η = penW Ωᵗ ζ y ys ν c (inj₁ (cmpΩ I)) η
```
