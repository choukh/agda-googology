# OmegaSqBase (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [OmegaSqBase](../../Align/OmegaSqBase.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.OmegaSqBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Symbolic using (Mlev; σ1)
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; z<suc; H1-pen; tr⁻ˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Free.Lab.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Free.Lab.Closure using (Pen; fsT₊-pen′)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; walk; walkD)
open import OCF.Free.Lab.Standard using (d₀)
open import OCF.Free.Lab.SystemOmega using (Occ; od; cmp-CΩ; Ctbl-suc)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.DecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              cofA; 𝟏) renaming (ψ to ψᵗ)
```

## §4 互模拟, 折叠方程, 记号

```agda
cmpΩ : ∀ {ν} → Idx ν → cmpᵀ (sucT ν) Ωᵗ ≡ lt
cmpΩ I = cmp-CΩ (Ctbl-suc (Idx-Ctbl I)) []
```

## §9 结论与边界
