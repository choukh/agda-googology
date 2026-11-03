# Uniform5Top (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform5Top](../../Align/Uniform5Top.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform5Top where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Lab0[])
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Free.Lab.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Uniform3Hon
open import OCF.Free.Lab.Uniform3Depth2Class
open import OCF.Free.Lab.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Free.Lab.Uniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Free.Lab.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Free.Lab.Uniform5Head
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Lab.Uniform5Class
open import OCF.Free.Lab.Uniform5Close
open import OCF.Free.Lab.Uniform5Tail
open import OCF.Free.Lab.Uniform5Tr
open import OCF.Free.Lab.Uniform5Psi
open import OCF.Free.Lab.Uniform5Rel
open import OCF.Free.Lab.Uniform5RelPsi
open import OCF.Free.Lab.Uniform3SqA using (LW0→LW)
open import OCF.Free.Lab.Uniform5Eval
open import OCF.Free.Lab.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Free.Lab.StandardOmega using (NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁)
open import OCF.Free.Lab.Closure using (lt→<; lt→<ᴾ; <→lt; <ᵀ-trans; cmpᵀ-refl; eq→≡; eq→≡ᴾ) renaming (Pen to CPen)
open import OCF.Free.Lab.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Free.Lab.SystemOmega using (cmp-CΩ)
open import OCF.Free.Lab.Uniform4Label using (nfΩp)
open import OCF.Free.Lab.Uniform4TwoWalk using (tΩ·2)
open import OCF.Free.Lab.Stage2 using () renaming (≺→⊑ to ≺→⊑²)
open import OCF.Free.Lab.Stage2Label using (Lab-oc)
open import OCF.Free.Lab.OmegaExpBase using (1<γ)
open import OCF.Free.Lab.Uniform5Label
open import OCF.Free.Lab.Uniform5Clo
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open GRᴬ
```

## §1 $\psi_0(\Omega_{\Omega\cdot2})$

```agda
yΩ·2 : PT
yΩ·2 = ψᵗ (Ωp ∷ Ωp ∷ []) []

γ₂ : ℕ → T
γ₂ = γW [] (yΩ·2 ∷ []) []

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
