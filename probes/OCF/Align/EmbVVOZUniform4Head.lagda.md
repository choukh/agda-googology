> **机械克隆, 验收用.** 由 `OrdLabZUniform4Head` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform4Head where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
import OCF.Align.EBO as E
open import OCF.Align.LadderLabZSystemOmega using (cmp-CΩ; cmp-ΩC; Ctbl-suc)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI)
open import OCF.Align.EmbVVOZOmegaSqBase using (cmpΩ)
open import OCF.Align.EmbVVOZOmegaExpBase using (πw; cofW; repW; ωW; γW; gtW; penW; fsnΣ; fsTΣ; predΣ; cofΣ)
open import OCF.Align.OrdLabZClosure using (Pen)
open import OCF.Align.EmbVVOZDecouple using (cofP)
open import OCF.Align.EmbVVOZGoodLBase using (Idx-Ctbl)
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
