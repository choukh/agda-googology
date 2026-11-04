# Uniform3 (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform3](LadderLabZUniform3.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; walk; t2-NF; tO-desc-NF)
open import OCF.Align.OrdLabZPrefix using (X₂-NF)
open import OCF.Align.OrdLabZSymbolic using (X₂ᵗ)
open import OCF.Align.OrdLabZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Lab-uniq)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ; t2)
open import OCF.Align.OrdLabZUniformS using (_≅ˢ_; z≅; s≅; upʳ; Ωˢ-refl; Ωˢ-≅; two)
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI)
open import OCF.Align.OrdLabZGoodLBase using (LabL; LabL₊; Ll; Lab0ᴸ; Atomᴸ; atomL; gs; gz; gu; lab1; nf1; LabL-Ω; I0; Lab→Ctbl; Idx-Ctbl; ctbl-hd; Goodᴸ; forceᴸ; toL₊)
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; repW)
open import OCF.Align.OrdLabZUniform3Base
open import OCF.Align.OrdLabZUniform3Depth1
```

```agda
open E using (T; PT; natT; fsT; cof; pred; c1; cΩ; Ωt; 𝟏) renaming (ψ to ψᵗ)
```

## §2 符号项层面的好性 (深度 0 与 1)

```agda
good∅ᴿ : GA0 ∅ᴿ []
good∅ᴿ = FlrLab-fz ,
         gr (λ { ev p (Y , hY , lY , nY) ei ki → toL₊ ki (LabL-Ω Y hY lY nY ei) })
            (λ ev p nf → gs gz , l1 refl (s≅ z≅) (l0 refl z≅))
            (λ ev p ev′ p′ ei → Ωˢ-≅ ei)
```

## §8 结论与边界
