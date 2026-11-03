# 统一形 (五): $\psi_0(\Omega_{\Omega\cdot2})$ 的标签

> 接 [Uniform5Clo](Uniform5Clo.lagda.md). `TΩ·2-label : Lab₀ (TΩ·2 ev p) tΩ·2`: 树是 Uniform4Two 的 `TΩ·2`, 未改动. 基本列 `fs-tΩ·2`: $\gamma_0=1$, $\gamma_{n+1}=\psi_0(\Omega_{\Omega+\gamma_n})$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Top where

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
open import OCF.Align.Uniform5Clo
```

## §1 $\psi_0(\Omega_{\Omega\cdot2})$

```agda
yΩ·2 : PT
yΩ·2 = ψᵗ (Ωp ∷ Ωp ∷ []) []

_ : tΩ·2 ≡ ψ₀ᵗ (yΩ·2 ∷ [])
_ = refl

_ : ∀ θ → fsT (yΩ·2 ∷ []) θ ≡ Ωs₊ θ
_ = λ θ → refl

_ : cof (yΩ·2 ∷ []) ≡ cΩ []
_ = refl

-- EBO 的链: γ₀ = 1, γ_{n+1} = ψ₀(Ω_{Ω+γ_n})
γ₂ : ℕ → T
γ₂ = γW [] (yΩ·2 ∷ []) []

_ : γ₂ 0 ≡ natT 1
_ = refl

_ : ∀ n → γ₂ (suc n) ≡ ψ₀ᵗ (Ωs₊ (γ₂ n))
_ = λ n → refl

fs-tΩ·2 : ∀ n → fsn tΩ·2 n ≡ ψ₀ᵗ (Ωs₊ (γ₂ n))
fs-tΩ·2 = gtW [] [] yΩ·2 [] [] refl refl

ctγ : ∀ m → Ctbl (γ₂ m)
ctγ zero = c∷ c[]
ctγ (suc m) = c∷ c[]

nfγ₂ : ∀ m → NF₁ (γ₂ m)
nfγ₂ zero = nf1
nfγ₂ (suc m) = NF-Ω (nfγ₂ m) (ctγ m)

monoγ₂ : ∀ m → γ₂ m <ᵗ γ₂ (suc m)
monoγ₂ zero = E.hd< (E.ar< E.[]<)
monoγ₂ (suc m) = E.hd< (E.ar< (E.hd< (E.lv< (E.tl< (monoγ₂ m)))))

fwΩ·2 : FW₀ (Fl ⊔ fk zero) [] yΩ·2 []
fwΩ·2 (inr ink) = inj₁ z≅
fwΩ·2 (inl (inr ink)) = inj₁ z≅

TΩ·2-label : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (p : zero <ᴵ ℓ) → Lab₀ (TΩ·2 ev p) tΩ·2
TΩ·2-label =
  clo† {φ = Fl} {ps = []} {y = yΩ·2} {ys = []} {t = wk 0 proj₁ (ψ̄ (Ω̇ (suc zero)))} {g = λ η → wk 0 proj₁ (ψ̄ (Ω̇ η))} fwΩ·2 refl (λ m → nfγ₂ (suc m))
       (λ m → E.hd< (E.ar< (E.hd< (E.lv< (E.tl< (monoγ₂ m))))))
       (wkO 0 {X = ψ̄ (Ω̇ (suc zero))} proj₁ (Ld→O (LdΩ̇ one⁰ (hs hz) lab1 nf1 (s≅ z≅) hon) (RΩ̇ (≅ᴵ-refl _))))
       (λ θ Y hY lY nθ lt → wkO 0 {X = ψ̄ (Ω̇ (toLevel Y hY))} proj₁ (Ld→O (LdΩ̇ Y hY lY nθ (≅ᴵ-refl _) hon) (RΩ̇ (≅ᴵ-refl _))))
```
