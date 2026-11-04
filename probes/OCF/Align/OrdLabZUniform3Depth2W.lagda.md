# Uniform3Depth2W (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform3Depth2W](LadderLabZUniform3Depth2W.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform3Depth2W where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Ord₊ˢ; Ordˢ; Ωˢ; intoˢ; toZ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base
open import OCF.Align.OrdLabZUniform3Depth1 using (cωΩ; cΩΩ; penΩ)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Full using (pred-Pr; flo≼)
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.LadderLabZUniform3Depth2W public using (fsTΩ)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
```

## §3 诚实的尾巴: `WH`, `WΩ`

```agda
CH : (j : Ordᴵ) → T → Ordˢ j → Set
CH j η x = kd j ≡ false → Hn x η × FH (flo j) η

InpW : (j : Ordᴵ) → T → Ordˢ j → Set
InpW j η x = LabL x η × CH j η x

FHν : ∀ {ν v j} (I : Idx ν) → j ≅ᴵ lvI I → FH (flo j) (ψᵗ ν v ∷ [])
FHν I e k = inj₂ (inj₂ (I , flo≼ e k))
```
