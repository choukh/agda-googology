> **机械克隆, 验收用.** 由 `OrdLabZUniform3` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform3 where

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
open import OCF.Align.EmbVVOZPrefix using (Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NF₁-fsn; walk; t2-NF; tO-desc-NF)
open import OCF.Align.EmbVVOZPrefix using (X₂-NF)
open import OCF.Align.OrdLabZSymbolic using (X₂ᵗ)
open import OCF.Align.EmbVVOZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Lab-uniq)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ; t2)
open import OCF.Align.EmbVVOZUniformS using (_≅ˢ_; z≅; s≅; upʳ; Ωˢ-refl; Ωˢ-≅; two)
open import OCF.Align.EmbVVOZDecoupleBase using (ΩΩ)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI)
open import OCF.Align.EmbVVOZGoodLBase using (LabL; LabL₊; Ll; Lab0ᴸ; Atomᴸ; atomL; gs; gz; gu; lab1; nf1; LabL-Ω; I0; Lab→Ctbl; Idx-Ctbl; ctbl-hd; Goodᴸ; forceᴸ; toL₊)
open import OCF.Align.EmbVVOZOmegaExpBase using (OccΣ; repW)
open import OCF.Align.EmbVVOZUniform3Base
open import OCF.Align.EmbVVOZUniform3Depth1
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
