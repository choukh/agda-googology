> **机械克隆.** 由 `Uniform5Close` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): 标签对加法封闭

> 接 [Uniform5Class](Uniform5Class.lagda.md). 与 [Uniform4Close](Uniform4Close.lagda.md) 逐行相同, 层号是 `Ordᴵ`. 地板的引理 (`FlU-⊔`, `Fw-⊕`) 字面不变.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform5Close where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ)
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two
open import OCF.Align.ScafLadderZUniform5Class
```

```agda
re : ∀ {c b m φ} {x : O c φ} {u v} → u ≡ v → Ld c b m x u → Ld c b m x v
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

FC-pre : ∀ {b c x} v → FC b c x → FC b c (x ++ v)
FC-pre {b = false} v F = tt
FC-pre {b = true}  v F = FlrLab-mono (OccPre v) F

Ld-⊕ : ∀ {c b b′ m φ ψ} {W : O c φ} {t : O c ψ} {x y} → Ld c b m W x → FlM m φ x → FC b c x → Ld c b′ m t y → Ld c b m (W ⊕ t) (x ++ y)
Ld-⊕ {x = x} lW F Fc lz = lwk (re (sym (++-identityʳ x)) lW)
Ld-⊕ {x = x} lW F Fc (ls {ps = ps} {y} {ys} cc Fa _ l) =
  re (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa)) (subst (FC _ _) (sym (++-assoc x ps _)) (FC-pre _ Fc)) (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc l)))
Ld-⊕ {x = x} lW F Fc (ll {ps = ps} {y} {ys} cc h) =
  re (++-assoc x ps (y ∷ ys)) (ll {ps = x ++ ps} cc (λ n → re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc (h n))))
Ld-⊕ {x = x} lW F Fc (li {ps = ps} {y} {ys} cc I e hP hI) =
  re (++-assoc x ps (y ∷ ys)) (li {ps = x ++ ps} cc I e
     (λ η z l s v → re (sym (++-assoc x ps _)) (Ld-⊕ (Ld-cv v lW) (FlM-cv v F) Fc (hP η z l s v)))
     (λ η z i → re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc (hI η z i))))
Ld-⊕ {x = x} lW F Fc (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  re (++-assoc x ps (y ∷ ys)) (lĉ {ps = x ++ ps} cc K (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc h₀)) (λ k → re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc (hk k))))
Ld-⊕ {x = x} lW F Fc (lŝ {ps = ps} {y} {ys} cc I b ob h₀ hg) =
  re (++-assoc x ps (y ∷ ys)) (lŝ {ps = x ++ ps} cc I b (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (ob θ)))
     (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc h₀))
     (λ θ Y hY lY nθ lt e → re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc (hg θ Y hY lY nθ lt e))))
Ld-⊕ {x = x} lW F Fc (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (re (++-assoc x ps (y ∷ ys)) (lclo {ps = x ++ ps} (Fw-⊕ F G) cc
     (lwk (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc h₀)))
     (λ θ Y hY lY nθ lt → lwk (re (sym (++-assoc x ps _)) (Ld-⊕ lW F Fc (hg θ Y hY lY nθ lt))))))
Ld-⊕ lW F Fc (lwk l) = lwk (Ld-⊕ lW F Fc l)
Ld-⊕ {x = x} lW F Fc (lΩ {ps = ps} {y} {ys} cc I e f) =
  re (++-assoc x ps (y ∷ ys)) (lΩ {ps = x ++ ps} cc I e
     (λ v ξ z θ l → lwk (re (sym (++-assoc x ps _)) (Ld-⊕ (Ld-cv v lW) (FlM-cv v F) Fc (f v ξ z θ l)))))
Ld-⊕ lW F Fc (lob l x) = Ld-⊕ lW F Fc x
```
