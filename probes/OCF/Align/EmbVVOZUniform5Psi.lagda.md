> **机械克隆, 验收用.** 由 `OrdLabZUniform5Psi` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform5Psi where

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
open import OCF.Align.EmbVVOZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW)
open import OCF.Align.OrdLabZClosure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.EmbVVLZStandardOmega using ()
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
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.EmbVVOZUniform5Head
open import OCF.Align.EmbVVOZUniform4Head using (module HeadRules)
open import OCF.Align.EmbVVOZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Free.Tree
open import OCF.Align.EmbVVOZUniform5Class
open import OCF.Align.EmbVVOZUniform5Close
open import OCF.Align.EmbVVOZUniform5Tr
open import OCF.Align.LadderLabZUniform5Psi public using (Pen-μ; occ-rep; rep-snoc′)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
```

## §1 重复

```agda
I₁ : Idx (natT 1)
I₁ = one⁰ , hs hz , lab1 , nf1

FlU→μ : ∀ {m φ b} (τ : T) → FlU m φ b → FlM m (Fl ⊔ φ) (ψᵗ (μ τ) b ∷ [])
FlU→μ {m = hon} t F (inl (inr ink)) = inj₁ z≅
FlU→μ {m = hon} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)
FlU→μ {m = wkm c} t F (inl (inr ink)) = inj₁ (inj₁ (inj₁ z≅))
FlU→μ {m = wkm c} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)

FlM-rep : ∀ {m φ x} n → FlM m φ (x ∷ []) → FlM m φ (replicate (suc n) x)
FlM-rep {m = hon} n F = FlrLab-mono (occ-rep n) F
FlM-rep {m = wkm c} n F = FlrLab[]-mono (occ-rep n) F

FC-rep : ∀ {b c x} n → FC b c (x ∷ []) → FC b c (replicate (suc n) x)
FC-rep {b = false} n F = tt
FC-rep {b = true}  n F = FlrLab-mono (occ-rep n) F
```

## §2 主定理

```agda
Fw-ψ : ∀ {m φ ps y ys} (τ : T) → cof (y ∷ ys) ≡ cΩ [] → Fw m (φ ⊔ fk zero) ps y ys →
       Fw m ((Fl ⊔ φ) ⊔ fk zero) [] (ψᵗ (μ τ) (ps ++ (y ∷ ys))) []
Fw-ψ {m = hon} τ cc G (inr ink) = inj₁ z≅
Fw-ψ {m = hon} τ cc G (inl (inl (inr ink))) = inj₁ z≅
Fw-ψ {m = hon} {ps = ps} {y} {ys} τ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (o θ)))
Fw-ψ {m = wkm c} τ cc G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} τ cc G (inl (inl (inr ink))) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} {ps = ps} {y} {ys} τ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (o θ)))
```
