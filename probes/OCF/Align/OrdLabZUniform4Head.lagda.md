# Uniform4Head (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform4Head](LadderLabZUniform4Head.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform4Head where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
import OCF.Align.EBO as E
open import OCF.Align.LadderLabZSystemOmega using (cmp-CΩ; cmp-ΩC; Ctbl-suc)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI)
open import OCF.Align.OrdLabZOmegaSqBase using (cmpΩ)
open import OCF.Align.OrdLabZOmegaExpBase using (πw; cofW; repW; ωW; γW; gtW; penW; fsnΣ; fsTΣ; predΣ; cofΣ)
open import OCF.Align.OrdLabZClosure using (Pen)
open import OCF.Align.OrdLabZDecouple using (cofP)
open import OCF.Align.OrdLabZGoodLBase using (Idx-Ctbl)
open import OCF.Align.LadderLabZUniform4Head public using (Ωp)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cofA; cmpᵀ; lt; eq; gt; Cmp) renaming (ψ to ψᵗ)
```

## §2 头 $h$ 上的规则

```agda
module HeadRules (h : T) {ps : T} {y : PT} {ys : T} where
  c1h : cof (y ∷ ys) ≡ c1 → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  c1h c = trans (cofW h ps y ys) (cong (cofA h) c)

  cωh : cof (y ∷ ys) ≡ cω → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  cωh c = trans (cofW h ps y ys) (cong (cofA h) c)

  cΩh : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) h) → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cΩ ν
  cΩh {ν} c p = trans (cofW h ps y ys) (trans (cong (cofA h) c) (cofP {w = h} {ν = ν} p))

  penh : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) h) → ∀ η → fsT (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) η ≡ ψᵗ h (ps ++ fsT (y ∷ ys) η) ∷ []
  penh {ν} c p η = penW h ps y ys ν c p η

  cgth : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) h ≡ gt → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  cgth {ν} c e = trans (cofW h ps y ys) (trans (cong (cofA h) c) (cong (E.cofψ₊ h ν) e))
```
