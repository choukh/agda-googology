# Uniform3SqA (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3SqA](../../Align/Uniform3SqA.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3SqA where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Free.Lab.Bachmann using (gt→<)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; walkD)
open import OCF.Free.Lab.Standard using (d₀)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.Stage2Label using (one⁰; Lab-oc)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Decouple using (Idx; lvI)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3Depth1 using (wkL0; cωΩ; cΩΩ; penΩ)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; []<; 𝟏) renaming (ψ to ψᵗ)

```

## §1 深度 1 的折叠定理 (目标 0 部分), 第 $\le2$ 层

```agda
FP0 : Flr → Set
FP0 φ = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one)

Up0 : ∀ {i w} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up zero i
Up0 {w = []} Iw ei ki = ⊥-elim (ne-w′ Iw ei ki)
  where
  ne-w′ : ∀ {i} (Iw : Idx []) → i ≅ᴵ lvI Iw → kd i ≡ false → ⊥
  ne-w′ Iw ei ki = tf (trans (sym (kdI[]′ Iw)) (trans (sym (kd-≅ ei)) ki))
    where
    kdI[]′ : (I : Idx []) → kd (lvI I) ≡ true
    kdI[]′ (Ord₊.zero , hY , lY , nY) = refl
    kdI[]′ (Ord₊.suc Y , hY , l0 c () , nY)
    kdI[]′ (Ord₊.suc Y , hY , l1 () e l , nY)
    kdI[]′ (Ord₊.suc Y , hY , lω () e h , nY)
    kdI[]′ (Ord₊.lim F , hY , l0 c () , nY)
    kdI[]′ (Ord₊.lim F , hY , l1 () e l , nY)
    kdI[]′ (Ord₊.lim F , hY , lω () e h , nY)
    kdI[]′ (Ord₊.limᵢ () f , hY , lY , nY)
    kdI[]′ (Ord₊.up () x , hY , lY , nY)
Up0 {w = x ∷ xs} (Y , hY , lY , nY) ei ki with one⊑lab hY lY nY []<
... | s⊑ e q = Up-≅ (inj₁ (via e q)) (≅ᴵ-sym ei)

LW0→LW : ∀ {φ} {R : Run φ} {u} → LW[ zero ] R u → LW R u
LW0→LW h ev p Iw ei ki = h ev p Iw ei ki (Up0 Iw ei ki)
```

## §4 新标签: $\psi_0(\Omega_\Omega\cdot\Omega_3)$ 与第 2 层指数
