# Uniform5Eval (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform5Eval](LadderLabZUniform5Eval.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform5Eval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ)
open import OCF.Align.OrdLabZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.OrdLabZClosure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.LadderLabZStandardOmega using ()
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.OrdLabZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.OrdLabZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.OrdLabZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.OrdLabZUniform5Head
open import OCF.Align.OrdLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Free.Tree
open import OCF.Align.OrdLabZUniform5Class
open import OCF.Align.OrdLabZUniform5Close
open import OCF.Align.OrdLabZUniform5Tr
open import OCF.Align.OrdLabZUniform5Psi
open import OCF.Align.OrdLabZUniform3SqA using (LW0→LW)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open GRᴬ
```

## §2 求值的 $W$ 部分

```agda
OkW : Mode → Ordᴵ → Set
OkW hon     c = ⊤
OkW (wkm i) c = Up i c

Cv-of : ∀ {m c i} → OkW m c → Up c i → Cv m (wkm i)
Cv-of {m = hon} ok u = cv-h
Cv-of {m = wkm i} ok u = cv-w (≼-trans ok u)

Fw→[] : ∀ {m c φ ps y ys} → OkW m c → Fw m φ ps y ys → FW[ c ] φ ps y ys
Fw→[] {m = hon} ok F = FW→FW[] F
Fw→[] {m = wkm i} ok F = Fw-cv (cv-w ok) F

inp₀ : ∀ {ν j} (I : Idx ν) → j ≅ᴵ lvI I → InpW j (Ωt ν) (Ωˢ j)
inp₀ I e = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) e , λ _ → hΩ refl I e , FHν I e
```

## §3 求值的 $L_0$ 部分与主定理
