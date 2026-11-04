> **机械克隆, 验收用.** 由 `OrdLabZUniform5Tr` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform5Tr where

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
open import OCF.Align.EmbVVOZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.EmbVVOZDecoupleBase using (ΩΩ)
open import OCF.Align.EmbVVOZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZOmegaExpBase using (OccΣ; cofΣ; predΣ)
open import OCF.Align.EmbVVOZGoodLBase
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.EmbVVOZUniform3Rel
open import OCF.Align.EmbVVOZUniform3SqABase
open import OCF.Align.EmbVVOZUniform3Hon
open import OCF.Align.EmbVVOZUniform3Depth2Class
open import OCF.Align.EmbVVOZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.EmbVVOZUniform3Depth2Fold using (Zc₀; Zc₀-of)
open import OCF.Align.EmbVVOZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr)
open import OCF.Align.EmbVVOZUniform5Head
open import OCF.Align.EmbVVOZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Free.Tree
open import OCF.Align.EmbVVOZUniform5Class
open import OCF.Align.EmbVVOZUniform5Close
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open RestrO
```

```agda
FC-≅ : ∀ {t a b u} → a ≅ᴵ b → FC t a u → FC t b u
FC-≅ {t = false} e F = tt
FC-≅ {t = true} {a = zero} {b = zero} z≅ F = λ ()
FC-≅ {t = true} {a = suc a} {b = suc b} (s≅ e) F ink with F ink
... | inj₁ e0 = inj₁ (≅ᴵ-trans (≅ᴵ-sym e) e0)
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , ≼-trans (inj₂ (≅ᴵ-sym e)) kw , o)
FC-≅ {t = true} {a = lim f s} {b = lim g r} e F inb with F inb
... | inj₁ ()
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , ≼-trans (inj₂ (≅ᴵ-sym e)) kw , o)
```
