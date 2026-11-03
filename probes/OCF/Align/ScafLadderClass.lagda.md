# 阶梯 (三): `P` 上的标签类

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 由 [Uniform5Class](Uniform5Class.lagda.md), [Uniform5Close](Uniform5Close.lagda.md), [Uniform5Tail](Uniform5Tail.lagda.md) 的克隆改写. `Lp` 与 `Ld` 同形, 多三行: `lcl` (高度 1 的闭包), `lΩ↓` (高度 1 的节点, 输入是 `Ld k true`), `lΩ` (高度 2 的节点). `ls` 多一项高度 1 的地板标签 `FlrLab χ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderClass where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
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
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.ScafLadderZStandardOmega using ()
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two renaming (ι to ιᵒ)
open import OCF.Align.ScafLadderZUniform5Class
open import OCF.Align.ScafLadderZUniform5Close
open import OCF.Align.ScafLadderZUniform5Tail
open import OCF.Align.ScafLadderZUniform5Tr
open import OCF.Align.ScafLadderZUniform5Psi
open import OCF.Align.ScafLadderZUniform5Rel
open import OCF.Align.ScafLadderZUniform5RelPsi
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.ScafLadderTree
open RestrP using ()
```

## §1 `Lp`

```agda
module _ (c : Ordᴵ) (L : ∀ {k} → k ◃ c → Mode → ∀ {ξ ζ} → P k ξ ζ → T → Set) where
  data Lp₊ : Mode → ∀ {φ χ} → P c φ χ → T → Set where
    lz : ∀ {m φ χ} → Lp₊ m {φ} {χ} p0 []
    ls : ∀ {m φ χ ps y ys} {a : P c φ χ} → cof (y ∷ ys) ≡ c1 → FlU m φ (ps ++ pred (y ∷ ys)) → FlrLab χ (ps ++ pred (y ∷ ys)) → Lp₊ m a (ps ++ pred (y ∷ ys)) → Lp₊ m (psu a) (ps ++ (y ∷ ys))
    ll : ∀ {m φ χ ps y ys} {F : ℕ → P c φ χ} → cof (y ∷ ys) ≡ cω → (∀ n → Lp₊ m (F n) (ps ++ fsn (y ∷ ys) n)) → Lp₊ m (pl F) (ps ++ (y ∷ ys))
    li : ∀ {m φ χ ps y ys ν j} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → P c φ χ} → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Cv m (wkm i) → Lp₊ (wkm i) (f x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → InpW j η x → Lp₊ m (f x) (ps ++ fsT (y ∷ ys) η)) → Lp₊ m (pi ac f) (ps ++ (y ∷ ys))
    lĉ : ∀ {m φ χ ps y ys c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₀ : P c φ χ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → P c φ χ} → cof (y ∷ ys) ≡ cω →
         (K : CCᴸ c₀ z zg) → Lp₊ m o₀ (ps ++ fsn (y ∷ ys) 0) →
         (∀ k → Lp₊ m (o (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Lp₊ m (pĉ c₀ z zg o₀ o) (ps ++ (y ∷ ys))
    lŝ : ∀ {m φ χ ps y ys c₀ w′} {t : P c φ χ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → P c φ χ} → cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys →
         Lp₊ m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Lp₊ m (g (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
         Lp₊ m (pŝ c₀ t g) (ps ++ (y ∷ ys))
    lclo : ∀ {m φ χ ps y ys} {t : P c (φ ⊔ fk zero) χ} {g : (η : Ordᴵ) → P c (φ ⊔ fk η) χ} → Fw m (φ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         Lp₊ m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Lp₊ m (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Lp₊ m (pclo t g) (ps ++ (y ∷ ys))
    lcl : ∀ {m φ χ ps y ys w₀} {t : P c φ (χ ⊔ fk zero)} {g : (η : Ordᴵ) → P c φ (χ ⊔ fk η)} → FW₀ (χ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         (I₀ : Idx w₀) → zero ≼ lvI I₀ → Ob w₀ ps y ys →
         Lp₊ m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Lp₊ m (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Lp₊ m (pcl t g) (ps ++ (y ∷ ys))
    lwk : ∀ {m φ φ′ χ χ′ u} {le : ∀ {L} → Ev L φ′ → Ev L φ} {le′ : ∀ {L} → Ev L χ′ → Ev L χ} {x : P c φ χ} → Lp₊ m x u → Lp₊ m (pwk le le′ x) u
    lΩ↓ : ∀ {m φ χ ps y ys k ν} {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L χ → k <ᴵ L} {h : ∀ ξ → O k ξ → P c (ξ ⊔ φ) χ} → cof (y ∷ ys) ≡ cΩ (μ ν) →
         (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → Ld k true m′ z θ → Lp₊ m′ (h ξ z) (ps ++ fsT (y ∷ ys) θ)) → Lp₊ m (pΩ↓ fe ac h) (ps ++ (y ∷ ys))
    lΩ : ∀ {m φ χ ps y ys k ν} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fc : ∀ {L} → Ev L χ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Vs k (<→◃ r) ξ ζ → P c (ξ ⊔ φ) (ζ ⊔ χ)} → cof (y ∷ ys) ≡ cΩ (μ (μ ν)) →
         (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ ζ (z : P k ξ ζ) θ → L (<→◃ r) m′ z θ → Lp₊ m′ (h ξ ζ (intoV (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) → Lp₊ m (pΩ fe fc r h) (ps ++ (y ∷ ys))

Lp : ∀ c → Mode → ∀ {φ χ} → P c φ χ → T → Set
Lq : ∀ c {k} → k ◃ c → Mode → ∀ {ξ ζ} → P k ξ ζ → T → Set
Lp c m x u = Lp₊ c (Lq c) m x u
Lq (suc c)   zero      m x u = Lp c m x u
Lq (suc c)   (suc r)   m x u = Lq c r m x u
Lq (lim f s) (self n)  m x u = Lp (f n) m x u
Lq (lim f s) (lim n r) m x u = Lq (f n) r m x u

outQ : ∀ {c k} (r : k ◃ c) {m ξ ζ} {z : P k ξ ζ} {θ} → Lq c r m z θ → Lp k m z θ
outQ zero      l = l
outQ (suc r)   l = outQ r l
outQ (self n)  l = l
outQ (lim n r) l = outQ r l

intoQ : ∀ {c k} (r : k ◃ c) {m ξ ζ} {z : P k ξ ζ} {θ} → Lp k m z θ → Lq c r m z θ
intoQ zero      l = l
intoQ (suc r)   l = intoQ r l
intoQ (self n)  l = l
intoQ (lim n r) l = intoQ r l

Lp-cv : ∀ {c a b φ χ} {x : P c φ χ} {u} → Cv a b → Lp c a x u → Lp c b x u
Lp-cv v lz = lz
Lp-cv v (ls cc F Fχ l) = ls cc (FlU-cv v F) Fχ (Lp-cv v l)
Lp-cv v (ll cc h) = ll cc (λ n → Lp-cv v (h n))
Lp-cv v (li cc I e hP hI) = li cc I e (λ η x l s v′ → hP η x l s (Cv-tr v v′)) (λ η x i → Lp-cv v (hI η x i))
Lp-cv v (lĉ cc K h₀ hk) = lĉ cc K (Lp-cv v h₀) (λ k → Lp-cv v (hk k))
Lp-cv v (lŝ cc I b ob′ h₀ hg) = lŝ cc I b ob′ (Lp-cv v h₀) (λ θ Y hY lY nθ lt e → Lp-cv v (hg θ Y hY lY nθ lt e))
Lp-cv v (lclo F cc h₀ hg) = lclo (Fw-cv v F) cc (Lp-cv v h₀) (λ θ Y hY lY nθ lt → Lp-cv v (hg θ Y hY lY nθ lt))
Lp-cv v (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lp-cv v h₀) (λ θ Y hY lY nθ lt → Lp-cv v (hg θ Y hY lY nθ lt))
Lp-cv v (lwk l) = lwk (Lp-cv v l)
Lp-cv v (lΩ↓ cc I e f) = lΩ↓ cc I e (λ v′ → f (Cv-tr v v′))
Lp-cv v (lΩ cc I e f) = lΩ cc I e (λ v′ → f (Cv-tr v v′))

rp : ∀ {c m φ χ} {x : P c φ χ} {u v} → u ≡ v → Lp c m x u → Lp c m x v
rp refl l = l
```

## §2 加法

```agda
FWχ-⊞ : ∀ {χ ρ x ps y ys} → FlrLab χ x → FW₀ (ρ ⊔ fk zero) ps y ys → FW₀ ((χ ⊔ ρ) ⊔ fk zero) (x ++ ps) y ys
FWχ-⊞ F G (inr ink) = inj₁ z≅
FWχ-⊞ {ps = ps} F G (inl (inl k)) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc _ ps _)) (OccPre _ o))
FWχ-⊞ {x = x} {ps = ps} F G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc x ps _)) (OccΣ x (o θ)))

Lp-⊞ : ∀ {c m φ χ ψ ρ} {W : P c φ χ} {t : P c ψ ρ} {x y} → Lp c m W x → FlM m φ x → FlrLab χ x → Lp c m t y → Lp c m (W ⊞ t) (x ++ y)
Lp-⊞ {x = x} lW F Fχ lz = lwk (rp (sym (++-identityʳ x)) lW)
Lp-⊞ {x = x} lW F Fχ (ls {ps = ps} {y} {ys} cc Fa Fb l) =
  rp (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa)) (subst (FlrLab _) (sym (++-assoc x ps _)) (FlrLab-⊔ Fχ Fb)) (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ l)))
Lp-⊞ {x = x} lW F Fχ (ll {ps = ps} {y} {ys} cc h) =
  rp (++-assoc x ps (y ∷ ys)) (ll {ps = x ++ ps} cc (λ n → rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (h n))))
Lp-⊞ {x = x} lW F Fχ (li {ps = ps} {y} {ys} cc I e hP hI) =
  rp (++-assoc x ps (y ∷ ys)) (li {ps = x ++ ps} cc I e
     (λ η z l s v → rp (sym (++-assoc x ps _)) (Lp-⊞ (Lp-cv v lW) (FlM-cv v F) Fχ (hP η z l s v)))
     (λ η z i → rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (hI η z i))))
Lp-⊞ {x = x} lW F Fχ (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  rp (++-assoc x ps (y ∷ ys)) (lĉ {ps = x ++ ps} cc K (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ h₀)) (λ k → rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (hk k))))
Lp-⊞ {x = x} lW F Fχ (lŝ {ps = ps} {y} {ys} cc I b o h₀ hg) =
  rp (++-assoc x ps (y ∷ ys)) (lŝ {ps = x ++ ps} cc I b (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (o θ)))
     (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ h₀))
     (λ θ Y hY lY nθ lt e → rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (hg θ Y hY lY nθ lt e))))
Lp-⊞ {x = x} lW F Fχ (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  rp (++-assoc x ps (y ∷ ys)) (lwk (lclo {ps = x ++ ps} (Fw-⊕ F G) cc
     (lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ h₀)))
     (λ θ Y hY lY nθ lt → lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (hg θ Y hY lY nθ lt))))))
Lp-⊞ {x = x} lW F Fχ (lcl {ps = ps} {y} {ys} G cc I₀ z₀ o h₀ hg) =
  rp (++-assoc x ps (y ∷ ys)) (lwk (lcl {ps = x ++ ps} (FWχ-⊞ Fχ G) cc I₀ z₀ (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (o θ)))
     (lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ h₀)))
     (λ θ Y hY lY nθ lt → lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ lW F Fχ (hg θ Y hY lY nθ lt))))))
Lp-⊞ lW F Fχ (lwk l) = lwk (Lp-⊞ lW F Fχ l)
Lp-⊞ {x = x} lW F Fχ (lΩ↓ {ps = ps} {y} {ys} cc I e f) =
  rp (++-assoc x ps (y ∷ ys)) (lΩ↓ {ps = x ++ ps} cc I e
     (λ v ξ z θ l → lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ (Lp-cv v lW) (FlM-cv v F) Fχ (f v ξ z θ l)))))
Lp-⊞ {x = x} lW F Fχ (lΩ {ps = ps} {y} {ys} cc I e f) =
  rp (++-assoc x ps (y ∷ ys)) (lΩ {ps = x ++ ps} cc I e
     (λ v ξ ζ z θ l → lwk (rp (sym (++-assoc x ps _)) (Lp-⊞ (Lp-cv v lW) (FlM-cv v F) Fχ (f v ξ ζ z θ l)))))
```

## §3 嵌入

```agda
out-intoV : ∀ {c k} (r : k ◃ c) {ξ ζ} (z : P k ξ ζ) → outV r (intoV r z) ≡ z
out-intoV zero      z = refl
out-intoV (suc r)   z = out-intoV r z
out-intoV (self n)  z = refl
out-intoV (lim n r) z = out-intoV r z

Lp-ι : ∀ {c d m φ χ} (q : c ◃ d) {x : P c φ χ} {u} → Lp c m x u → Lp d m (ι q x) u
Lp-ι q lz = lz
Lp-ι q (ls cc F Fχ l) = ls cc F Fχ (Lp-ι q l)
Lp-ι q (ll cc h) = ll cc (λ n → Lp-ι q (h n))
Lp-ι q (li cc I e hP hI) = li cc I e (λ η x l s v → Lp-ι q (hP η x l s v)) (λ η x i → Lp-ι q (hI η x i))
Lp-ι q (lĉ cc K h₀ hk) = lĉ cc K (Lp-ι q h₀) (λ k → Lp-ι q (hk k))
Lp-ι q (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lp-ι q h₀) (λ θ Y hY lY nθ lt e → Lp-ι q (hg θ Y hY lY nθ lt e))
Lp-ι q (lclo F cc h₀ hg) = lclo F cc (Lp-ι q h₀) (λ θ Y hY lY nθ lt → Lp-ι q (hg θ Y hY lY nθ lt))
Lp-ι q (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lp-ι q h₀) (λ θ Y hY lY nθ lt → Lp-ι q (hg θ Y hY lY nθ lt))
Lp-ι q (lwk l) = lwk (Lp-ι q l)
Lp-ι q (lΩ↓ cc I e f) = lΩ↓ cc I e (λ v ξ z θ l → Lp-ι q (f v ξ z θ l))
Lp-ι {d = d} q (lΩ {ps = ps} {y} {ys} {r = r} {h = h} cc I e f) =
  lΩ {r = <◃ r q} cc I e
     (λ {m′} v ξ ζ z θ l → subst (λ w → Lp d m′ (ι q (h ξ ζ (intoV (<→◃ r) w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoV (<→◃ (<◃ r q)) z))
                               (Lp-ι q (f v ξ ζ z θ (intoQ (<→◃ r) (outQ (<→◃ (<◃ r q)) l)))))

-- `ι↓`: `true` 档的 `Ld`
Lp-ι↓ : ∀ {k α m φ} {x : O k φ} {u} → Ld k true m x u → Lp α m (ι↓ {α = α} x) u
Lp-ι↓ lz = lz
Lp-ι↓ (ls cc F Fc l) = ls cc F Fc (Lp-ι↓ l)
Lp-ι↓ (ll cc h) = ll cc (λ n → Lp-ι↓ (h n))
Lp-ι↓ (li cc I e hP hI) = li cc I e (λ η x l s v → Lp-ι↓ (hP η x l s v)) (λ η x i → Lp-ι↓ (hI η x i))
Lp-ι↓ (lĉ cc K h₀ hk) = lĉ cc K (Lp-ι↓ h₀) (λ k → Lp-ι↓ (hk k))
Lp-ι↓ (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lp-ι↓ h₀) (λ θ Y hY lY nθ lt e → Lp-ι↓ (hg θ Y hY lY nθ lt e))
Lp-ι↓ (lclo F cc h₀ hg) = lclo F cc (Lp-ι↓ h₀) (λ θ Y hY lY nθ lt → Lp-ι↓ (hg θ Y hY lY nθ lt))
Lp-ι↓ (lwk l) = lwk (Lp-ι↓ l)
Lp-ι↓ (lΩ {r = r} cc I e f) = lΩ↓ cc I e (λ v ξ z θ l → Lp-ι↓ (f v ξ z θ (intoL (<→◃ r) l)))
Lp-ι↓ (lob {r = zero} l x) = lwk (Lp-ι↓ l)
Lp-ι↓ (lob {r = self n} l x) = lwk (Lp-ι↓ l)
```

## §4 $\Omega_{\Omega\cdot2+\theta}$

```agda
I₁ᵖ : Idx (natT 1)
I₁ᵖ = one⁰ , hs hz , lab1 , nf1

z≼1 : zero ≼ lvI I₁ᵖ
z≼1 = inj₁ (via z≅ zero)

Fw-cl : FW₀ (fz ⊔ fk zero) [] (ψᵗ (Ωp ∷ Ωp ∷ []) []) []
Fw-cl (inr ink) = inj₁ z≅

LpΩ̇ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ m → Lp α m (Ω̇ᴾ α) (Ωt (μ (μ θ)))
LpΩ̇ {θ = []} Ord₊.zero hY l nθ z≅ m =
  lcl {ps = []} {y = ψᵗ (Ωp ∷ Ωp ∷ []) []} {ys = []} Fw-cl refl I₁ᵖ z≼1 (λ θ → os oh)
      (lwk (Lp-ι↓ (LdΩ̇ one⁰ (hs hz) lab1 nf1 (s≅ z≅) m)))
      (λ θ Y hY lY nθ lt → lwk (Lp-ι↓ (LdΩ̇ Y hY lY nθ (≅ᴵ-refl _) m)))
LpΩ̇ {θ = w ∷ ws} Ord₊.zero hY l nθ z≅ m with Lab0[] l
... | ()
LpΩ̇ (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) m
LpΩ̇ (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) m
LpΩ̇ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) m
LpΩ̇ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {suc j} (s≅ e) m =
  lΩ {ps = []} {y = ψᵗ (μ (μ (w ∷ ws))) []} {ys = []} (cong (E.cofψ0 (μ (μ (w ∷ ws)))) c₁) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
     (λ v ξ ζ z θ l′ → lwk (rp (sym (fsTΩ {Ωp} {Ωp ∷ w ∷ ws} c₁ θ)) (Lp-ι zero l′)))
LpΩ̇ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) m
LpΩ̇ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) m
LpΩ̇ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) m
LpΩ̇ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {lim f s} (l≅ ee) m =
  ll {ps = []} {y = ψᵗ (μ (μ (w ∷ ws))) []} {ys = []} (cong (E.cofψ0 (μ (μ (w ∷ ws)))) c₁)
     (λ n → rp (sym (E.fsn0-eq Ωp (Ωp ∷ w ∷ ws) n c₁))
               (Lp-ι (self n) (LpΩ̇ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) m)))

LpΩ̇ᴵ : ∀ {ν α} (I : Idx ν) → α ≅ᴵ lvI I → ∀ m → Lp α m (Ω̇ᴾ α) (Ωt (μ (μ ν)))
LpΩ̇ᴵ (Y , hY , lY , nY) e m = LpΩ̇ Y hY lY nY e m
```
