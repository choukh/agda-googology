# Uniform5Close (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform5Close](../../Align/Uniform5Close.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform5Close where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab)
open import OCF.Free.Lab.StandardOmega using (NF₁)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Decouple using (Idx; lvI)
open import OCF.Free.Lab.OmegaExpBase using (OccΣ)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Uniform3Hon
open import OCF.Free.Lab.Uniform3Depth2Class
open import OCF.Free.Lab.Uniform3Depth2W using (InpW; CH; FHν)
open import OCF.Free.Lab.Uniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Free.Lab.Uniform5Head
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Lab.Uniform5Class
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
```

```agda
re : ∀ {c m φ} {x : O c φ} {u v} → u ≡ v → Ld c m x u → Ld c m x v
re refl l = l

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

Ld-⊕ : ∀ {c m φ ψ} {W : O c φ} {t : O c ψ} {x y} → Ld c m W x → FlM m φ x → Ld c m t y → Ld c m (W ⊕ t) (x ++ y)
Ld-⊕ {x = x} lW F lz = lwk (re (sym (++-identityʳ x)) lW)
Ld-⊕ {x = x} lW F (ls {ps = ps} {y} {ys} cc Fa l) =
  re (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa)) (re (sym (++-assoc x ps _)) (Ld-⊕ lW F l)))
Ld-⊕ {x = x} lW F (ll {ps = ps} {y} {ys} cc h) =
  re (++-assoc x ps (y ∷ ys)) (ll {ps = x ++ ps} cc (λ n → re (sym (++-assoc x ps _)) (Ld-⊕ lW F (h n))))
Ld-⊕ {x = x} lW F (li {ps = ps} {y} {ys} cc I e hP hI) =
  re (++-assoc x ps (y ∷ ys)) (li {ps = x ++ ps} cc I e
     (λ η z l s v → re (sym (++-assoc x ps _)) (Ld-⊕ (Ld-cv v lW) (FlM-cv v F) (hP η z l s v)))
     (λ η z i → re (sym (++-assoc x ps _)) (Ld-⊕ lW F (hI η z i))))
Ld-⊕ {x = x} lW F (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  re (++-assoc x ps (y ∷ ys)) (lĉ {ps = x ++ ps} cc K (re (sym (++-assoc x ps _)) (Ld-⊕ lW F h₀)) (λ k → re (sym (++-assoc x ps _)) (Ld-⊕ lW F (hk k))))
Ld-⊕ {x = x} lW F (lŝ {ps = ps} {y} {ys} cc I b ob h₀ hg) =
  re (++-assoc x ps (y ∷ ys)) (lŝ {ps = x ++ ps} cc I b (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (ob θ)))
     (re (sym (++-assoc x ps _)) (Ld-⊕ lW F h₀))
     (λ θ Y hY lY nθ lt e → re (sym (++-assoc x ps _)) (Ld-⊕ lW F (hg θ Y hY lY nθ lt e))))
Ld-⊕ {x = x} lW F (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (re (++-assoc x ps (y ∷ ys)) (lclo {ps = x ++ ps} (Fw-⊕ F G) cc
     (lwk (re (sym (++-assoc x ps _)) (Ld-⊕ lW F h₀)))
     (λ θ Y hY lY nθ lt → lwk (re (sym (++-assoc x ps _)) (Ld-⊕ lW F (hg θ Y hY lY nθ lt))))))
Ld-⊕ lW F (lwk l) = lwk (Ld-⊕ lW F l)
Ld-⊕ {x = x} lW F (lΩ {ps = ps} {y} {ys} cc I e f) =
  re (++-assoc x ps (y ∷ ys)) (lΩ {ps = x ++ ps} cc I e
     (λ v ξ z θ l → lwk (re (sym (++-assoc x ps _)) (Ld-⊕ (Ld-cv v lW) (FlM-cv v F) (f v ξ z θ l)))))
```
