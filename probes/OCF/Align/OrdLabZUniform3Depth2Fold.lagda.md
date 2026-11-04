# Uniform3Depth2Fold (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform3Depth2Fold](LadderLabZUniform3Depth2Fold.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform3Depth2Fold where

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
open import OCF.Align.OrdLabZPrefix using (Ord₊ˢ; Ordˢ; Ωˢ; intoˢ; toZ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZStage2Label using (one⁰)
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Ieq; Lab0[])
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base
open import OCF.Align.OrdLabZUniform3Depth1 using (cωΩ; cΩΩ; penΩ)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3SqA using (FP0; Up0)
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Full using (FH-pred; pred-Pr; flo≼)
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.OrdLabZUniform3Depth2W
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
```

## §2 目标 0 与折叠定理

```agda
Zc₀ : Ordᴵ → Flr → Set
Zc₀ zero φ = FP0 φ
Zc₀ (suc _) φ = ⊤
Zc₀ (lim _ _) φ = ⊤

Zc₀-of : ∀ {k φ w} (I : Idx w) → k ≅ᴵ lvI I → FH φ (Ωt w) → Zc₀ k φ
Zc₀-of {k = zero} I e f k₁ with f k₁
... | inj₁ e0 = inj₁ e0
... | inj₂ (inj₁ e1) = inj₂ e1
... | inj₂ (inj₂ (I′ , kw)) with ≼-trans kw (inj₂ (≅ᴵ-trans (Ieq I′ I) (≅ᴵ-sym e)))
...   | inj₁ (via _ ())
...   | inj₂ e0 = inj₁ e0
Zc₀-of {k = suc _} I e f = tt
Zc₀-of {k = lim _ _} I e f = tt

InpO : (j : Ordᴵ) → T → Ordˢ j → Set
InpO j η x = LabL x η × (x ≅ᴬ x) × CH j η x
```

## §4 主定理
