# 统一形 (四): 标签对加法封闭

> 接 [Uniform4Class](Uniform4Class.lagda.md). `Ld-⊕`: $W$ 带标签 $x$ (地板 `FlM m φ x`), $t$ 带标签 $y$, 则 $W\oplus t$ 带标签 $x+y$. 证明是 `Ld` 上的结构递归, 前缀 $ps$ 换成 $x+ps$; `li` 的穿透字段与 `lΩ` 的字段都把 $W$ 经 `Ld-cv` 转到新模式. 地板: `lclo` 处前缀的地板由 `FlM` 见证 (`Fw-⊕`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Close where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.StandardOmega using (NF₁)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI)
open import OCF.Align.OmegaExpBase using (OccΣ)
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.Uniform4Head
open import OCF.Align.Uniform4Base
open import OCF.Align.Uniform4Class
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
Ld-⊕ {x = x} lW F (lΩ {ps = ps} {y} {ys} cc b f) =
  re (++-assoc x ps (y ∷ ys)) (lΩ {ps = x ++ ps} cc b
     (λ v ξ z θ l → lwk (re (sym (++-assoc x ps _)) (Ld-⊕ (Ld-cv v lW) (FlM-cv v F) (f v ξ z θ l)))))
```
