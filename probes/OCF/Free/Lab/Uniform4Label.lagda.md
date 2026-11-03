# Uniform4Label (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform4Label](../../Align/Uniform4Label.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform4Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≡-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Free.Lab.StandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; bnd[]; Flat; f[]; f∷; f1; flatBnd; NF₁-fsn; NF₁-pred)
open import OCF.Free.Lab.Standard using (Ctbl; c[]; c∷)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Lab0[])
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW; fsnΣ)
open import OCF.Free.Lab.Closure using (cmpᵀ-refl; cmpᴾ-refl) renaming (Pen to CPen)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Uniform3Hon
open import OCF.Free.Lab.Uniform3Depth2Class
open import OCF.Free.Lab.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Free.Lab.Uniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Free.Lab.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Free.Lab.Uniform4Head
open import OCF.Free.Tree
open import OCF.Free.Lab.Uniform3SqA using (LW0→LW)
open import OCF.Free.Lab.StandardOmega using (Vis₁; vh; vd; vs; vt)
open import OCF.Free.Lab.Stage2 using (Lab-uniq)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open GRᴬ
```

## §1 标准形, 对 $c$ 一致

```agda
nfΩp : NFᴾ₁ Ωp
nfΩp = nψ nf1 (sC (c∷ c[])) n[] bnd[]
```

## §4 与 Uniform3 的对照
