# Uniform3Depth1 (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3Depth1](../../Align/Uniform3Depth1.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3Depth1 where

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
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Symbolic using (Mlev; Fs; Fst)
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ; H1-pen; H1-fsT)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Free.Lab.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Free.Lab.Closure using (Pen; fsT₊-pen′)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Free.Lab.Standard using (Ctbl; c[]; c∷)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot; occ<)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Stage2Label using (one⁰; Lab-oc)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP; Lab0[])
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq; gtW; penW; H1W; ne-w; 1<γ; ++-ne; fsT-ne)
open import OCF.Free.Lab.OmegaSqBase using (cmpΩ)
open import OCF.Free.Lab.Uniform3Base
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
