# Uniform3Depth2W (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3Depth2W](../../Align/Uniform3Depth2W.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3Depth2W where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; intoˢ; toZ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Lab0[])
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3Depth1 using (cωΩ; cΩΩ; penΩ)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Uniform3Hon
open import OCF.Free.Lab.Uniform3Full using (pred-Pr; flo≼)
open import OCF.Free.Lab.Uniform3Depth2Class
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
```

## §3 诚实的尾巴: `WH`, `WΩ`

```agda
fsTΩ : ∀ {w ws} → cof (w ∷ ws) ≡ c1 → ∀ η → fsT (Ωt (w ∷ ws)) η ≡ η
fsTΩ {w} {ws} c₁ η = fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c₁ η

CH : (j : Ordᴵ) → T → Ordˢ j → Set
CH j η x = kd j ≡ false → Hn x η × FH (flo j) η

InpW : (j : Ordᴵ) → T → Ordˢ j → Set
InpW j η x = LabL x η × CH j η x

FHν : ∀ {ν v j} (I : Idx ν) → j ≅ᴵ lvI I → FH (flo j) (ψᵗ ν v ∷ [])
FHν I e k = inj₂ (inj₂ (I , flo≼ e k))
```
