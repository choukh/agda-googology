# 统一形 (五): 顶层一步, 不要顶层 `NF₁` 的闭包行

> 接 [Uniform5Label](Uniform5Label.lagda.md). `clo†` 是 `clo0` (Uniform3Base) 的 `L0` 部分, 只把 "顶层 `NF₁` ⟹ 基本列 `NF₁` 与单调" 这一处换成假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Clo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.StandardOmega using ()
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.Uniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.Uniform5Head
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open import OCF.Align.Uniform5Class
open import OCF.Align.Uniform5Close
open import OCF.Align.Uniform5Tail
open import OCF.Align.Uniform5Tr
open import OCF.Align.Uniform5Psi
open import OCF.Align.Uniform5Rel
open import OCF.Align.Uniform5RelPsi
open import OCF.Align.Uniform3SqA using (LW0→LW)
open import OCF.Align.Uniform5Eval
open GRᴬ
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.StandardOmega using (NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <→lt; <ᵀ-trans; cmpᵀ-refl; eq→≡; eq→≡ᴾ) renaming (Pen to CPen)
open import OCF.Align.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.SystemOmega using (cmp-CΩ)
open import OCF.Align.Uniform4Label using (nfΩp; nf𝟏)
open import OCF.Align.Uniform4TwoWalk using (tΩ·2; ¬NF-Ω·2)
open import OCF.Align.Stage2 using () renaming (≺→⊑ to ≺→⊑²)
open import OCF.Align.Stage2Label using (Lab-oc)
open import OCF.Align.OmegaExpBase using (1<γ)
open import OCF.Align.Uniform5Label
```

```agda
ĉᴸ-mk† : ∀ {u c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → cof u ≡ cω → (nfs : ∀ n → NF₁ (fsn u n)) → (mono : ∀ n → fsn u n <ᵗ fsn u (suc n)) → (K : CCᴸ c t₀ g) →
         (Go₀ : Goodᴸ o₀) → Lab (forceᴸ _ Go₀) (fsn u 0) →
         (Go : ∀ k → Goodᴸ (o (lvK K k) (dxK K k))) → (∀ k → Lab (forceᴸ _ (Go k)) (fsn u (suc k))) →
         Σ (Goodᴸ (Z.ĉᴸ c t₀ g o₀ o)) λ G → Lab (forceᴸ _ G) u
ĉᴸ-mk† c nfs mono K Go₀ l₀ Go lk =
  gc (CCᴸ.γ K) (CCᴸ.G₀ K) (CCᴸ.l₀ K) (CCᴸ.d₀ K) (CCᴸ.Gg K) (CCᴸ.lE K) (CCᴸ.dE K) Go₀ Go
     (≺→⊑² (Lab-oc (lk 0) (nfs 1) l₀ (nfs 0) (mono 0)))
     (λ k → ≺→⊑² (Lab-oc (lk (suc k)) (nfs (suc (suc k))) (lk k) (nfs (suc k)) (mono (suc k)))) ,
  lω c (l≅ (λ n → ≅-refl⁰ _)) (outsLab l₀ lk)

module _ {φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW₀ (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ [])
         (nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m))))
         (monoγ : ∀ m → ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)) <ᵗ ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] (suc m)))) where

  clo† : L0 t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → L0 (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ {ℓ} (ev : Ev ℓ (φ ⊔ fk zero)) (p : zero <ᴵ ℓ) → Lab₀ (cloA 0 t g ev p) (ψ₀ᵗ (ps ++ (y ∷ ys)))
  clo† h₀ hg ev p =
    ĉᴸ-mk† cω′
          (λ n → subst NF₁ (sym (gtW [] ps y ys [] cs refl n)) (nfγ n))
          (λ n → subst₂ _<ᵗ_ (sym (gtW [] ps y ys [] cs refl n)) (sym (gtW [] ps y ys [] cs refl (suc n))) (monoγ n))
          K (proj₁ R₀) (subst (Lab _) (sym (gtW [] ps y ys [] cs refl 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] cs refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    B = bound (φ ⊔ fk zero) ev p
    cω′ = trans (cofW [] ps y ys) (cong (E.cofA []) cs)
    R₀ = h₀ ev p (nfγ 0)
    dom : ∀ {ℓ Y} (hY : HS Y) (B : Top zero ℓ (φ ⊔ fk zero)) → ∀ θ → Lab Y (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → Bd B ⊑ᴵ toLevel Y hY
    dom = domC {φ} {ps} {y} {ys} {t} {g} fw cs
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : Bd B ⊑ᴵ toLevel Y hY) →
         Lab₀ (g (toLevel Y hY) (evη φ B (toLevel Y hY) e) (lim 0 (iF B))) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (dom _ B (natT 1) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → dom _ B (γW ps (y ∷ ys) [] (suc m)) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))
```
