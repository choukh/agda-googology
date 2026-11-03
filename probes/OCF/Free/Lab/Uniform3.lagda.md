# Uniform3 (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3](../../Align/Uniform3.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; walk; t2-NF)
open import OCF.Free.Lab.Prefix using (X₂-NF)
open import OCF.Free.Lab.Symbolic using (X₂ᵗ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.Stage2 using (Lab-uniq)
open import OCF.Free.Lab.Standard using (c[]; c∷)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Stage2 using (Ωᵗ; t2)
open import OCF.Free.Lab.UniformS using (_≅ˢ_; z≅; s≅; upʳ; Ωˢ-refl; Ωˢ-≅; two)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Decouple using (Idx; lvI)
open import OCF.Free.Lab.GoodLBase using (LabL; LabL₊; Ll; Lab0ᴸ; Atomᴸ; atomL; gs; gz; gu; lab1; nf1; LabL-Ω; I0; Lab→Ctbl; Idx-Ctbl; ctbl-hd; Goodᴸ; forceᴸ; toL₊)
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; repW)
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3Depth1
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
