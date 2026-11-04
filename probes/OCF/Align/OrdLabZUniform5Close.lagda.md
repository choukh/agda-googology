# Uniform5Close (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform5Close](LadderLabZUniform5Close.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform5Close where

open import Data.Nat using (ℕ; zero; suc)
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
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI)
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ)
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.OrdLabZUniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.OrdLabZUniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.OrdLabZUniform5Head
open import OCF.Align.OrdLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Free.Tree
open import OCF.Align.OrdLabZUniform5Class
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
```

```agda
FlM→U : ∀ {m φ u} → FlM m φ u → FlU m φ u
FlM→U {m = hon} F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (inj₂ (w , Iw , kw , o))
FlM→U {m = wkm c} F k with F k
... | inj₁ g = inj₁ g
... | inj₂ (w , Iw , kw , o) = inj₂ (inj₂ (w , Iw , kw , o))

FlU-mono : ∀ {m φ u v} → (∀ {w} → Occ w u → Occ w v) → FlU m φ u → FlU m φ v
FlU-mono {m = hon} f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (inj₂ (w , Iw , kw , f o))
FlU-mono {m = wkm c} f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (inj₂ (w , Iw , kw , f o))

FlU-⊔ : ∀ {m φ ψ x u} → FlM m φ x → FlU m ψ u → FlU m (φ ⊔ ψ) (x ++ u)
FlU-⊔ {m = hon} {u = u} F G (inl k) = FlU-mono {m = hon} (OccPre u) (FlM→U {m = hon} F) k
FlU-⊔ {m = hon} {x = x} F G (inr k) = FlU-mono {m = hon} (OccΣ x) G k
FlU-⊔ {m = wkm c} {u = u} F G (inl k) = FlU-mono {m = wkm c} (OccPre u) (FlM→U {m = wkm c} F) k
FlU-⊔ {m = wkm c} {x = x} F G (inr k) = FlU-mono {m = wkm c} (OccΣ x) G k

FlM-⊔ : ∀ {m φ ψ x u} → FlM m φ x → FlM m ψ u → FlM m (φ ⊔ ψ) (x ++ u)
FlM-⊔ {m = hon} = FlrLab-⊔
FlM-⊔ {m = wkm c} = FlrLab[]-⊔

Fw-⊕ : ∀ {m φ ψ x ps y ys} → FlM m φ x → Fw m (ψ ⊔ fk zero) ps y ys → Fw m ((φ ⊔ ψ) ⊔ fk zero) (x ++ ps) y ys
Fw-⊕ {m = hon} F G (inr ink) = inj₁ z≅
Fw-⊕ {m = hon} {ps = ps} F G (inl (inl k)) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc _ ps _)) (OccPre _ o))
Fw-⊕ {m = hon} {x = x} {ps = ps} F G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc x ps _)) (OccΣ x (o θ)))
Fw-⊕ {m = wkm c} F G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-⊕ {m = wkm c} {ps = ps} F G (inl (inl k)) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc _ ps _)) (OccPre _ o))
Fw-⊕ {m = wkm c} {x = x} {ps = ps} F G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc x ps _)) (OccΣ x (o θ)))

FC-pre : ∀ {b c x} v → FC b c x → FC b c (x ++ v)
FC-pre {b = false} v F = tt
FC-pre {b = true}  v F = FlrLab-mono (OccPre v) F
```
