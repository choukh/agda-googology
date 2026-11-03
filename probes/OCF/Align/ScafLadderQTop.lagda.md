# 阶梯 (十三): 塔上的标签定理

> 结论写在 [ScafLadder](ScafLadder.lagda.md). `TΩᵠ-label m`: 对每个 $m$ 同一条定理, 无条件. 与 `Tᴾ` 的两棵树经 `Lab-uniq` $\cong$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderQTop where

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
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.ScafLadderZStandardOmega using ()
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_; Ψ) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.ScafLadderZUniform5Class using (hon; FlU)
open import OCF.Align.ScafLadderQ
open import OCF.Align.ScafLadderQClass
open import OCF.Align.ScafLadderQRel using (RΩ̇)
open import OCF.Align.ScafLadderQEval
open import OCF.Align.ScafLadderTop using (TΩ₂-label)
open import OCF.Align.ScafLadderNF using (NF-Ωᵐ)
import OCF.Align.ScafLadderTree as PT
open import OCF.Align.Stage2 using (Lab-uniq) renaming (≺→⊑ to ≺→⊑²)
open import OCF.Align.ScafLadderZStandardOmega using (n[]; n∷; nψ; sC; sΩ; bnd[]; vh; vd; vs; vt; Bnd₁)
open import OCF.Align.ScafLadderZStage2Label using (Lab-oc)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.ScafLadderQRel using (rs; rz)
open import OCF.Align.ScafLadderZOmegaExpBase using (repW; ωW)

B : ℕ → T
B m = ψ₀ᵗ (Ωt (Ωᵉ (suc (suc m)) []))

-- 一切 m, 一切低于 ψ₀(Ω_{Ω·(m+2)}) 的 θ
TΩᵠ-label : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B m → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ m α ev p) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) θ)))
TΩᵠ-label m Y hY lY nθ pm e = labelᵠ (LqΩ̇ m Y hY lY nθ e hon) (RΩ̇ m (≅ᴵ-refl _)) ok₀ (λ i h r → ok₀ i) (NF-Ωᵐ m nθ (Lab→Ctbl lY nθ) pm)

-- ψ₀(Ω_{Ω·(m+1)}): 一切 m
TΩ·-label : ∀ m {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ m zero ev p) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) [])))
TΩ·-label m = TΩᵠ-label m Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

-- ψ₀(Ω_{Ω·(m+1)+1})
TΩ·+1-label : ∀ m {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ m (suc zero) ev p) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) (natT 1))))
TΩ·+1-label m = TΩᵠ-label m one⁰ (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≅ z≅)

-- 任务的目标
TΩ·2+1 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ 1 (suc zero) ev p) (ψ₀ᵗ (Ωt (sucT (Ωp ∷ Ωp ∷ []))))
TΩ·2+1 = TΩ·+1-label 1

TΩ·3 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tᵠ 2 zero ev p) (ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ [])))
TΩ·3 = TΩ·-label 2

-- 与 P 上的树一致 (同一个标签)
agree-Ω₂ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) (lY : Lab Y θ) (nθ : NF₁ θ) (pm : θ <ᵗ B 1) → ∀ {ℓ ℓ′} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
           forceᴸ _ (proj₁ (TΩᵠ-label 1 Y hY lY nθ pm (≅ᴵ-refl _) ev p)) ≅ forceᴸ _ (proj₁ (TΩ₂-label Y hY lY nθ pm (≅ᴵ-refl _) ev′ p′))
agree-Ω₂ Y hY lY nθ pm ev p ev′ p′ = Lab-uniq (proj₂ (TΩᵠ-label 1 Y hY lY nθ pm (≅ᴵ-refl _) ev p)) (proj₂ (TΩ₂-label Y hY lY nθ pm (≅ᴵ-refl _) ev′ p′))

```

## $\psi_0(\Omega_{\Omega\cdot\omega})$

`tω` 不在 `NF₁`, 因为 `Sb` 不含 $\psi_1(1)$. 但它的基本列全在, 所以顶层一步仿 [Uniform5Clo](Uniform5Clo.lagda.md): 单调直接由 `Lab-oc` 给, 不经 `limᴸ`.

```agda
ψ₁1 : T
ψ₁1 = ψᵗ (natT 1) (natT 1) ∷ []

tω : T
tω = ψ₀ᵗ (Ωt ψ₁1)

rep-Ω : ∀ n → replicate n Ωp ≡ Ωᵉ n []
rep-Ω zero = refl
rep-Ω (suc n) = cong (Ωp ∷_) (rep-Ω n)

fs-ψ₁ : ∀ n → fsn ψ₁1 n ≡ Ωᵉ n []
fs-ψ₁ n = trans (repW (natT 1) [] 𝟏 [] refl n) (rep-Ω n)

fs-Ωt : ∀ n → fsn (Ωt ψ₁1) n ≡ Ωt (Ωᵉ n [])
fs-Ωt n = trans (E.fsn0-eq (ψᵗ (natT 1) (natT 1)) [] n refl) (cong (λ x → ψᵗ x [] ∷ []) (fs-ψ₁ n))

cω-tω : cof tω ≡ cω
cω-tω = refl

fs-tω : ∀ n → fsn tω n ≡ ψ₀ᵗ (Ωt (Ωᵉ n []))
fs-tω n = trans (ωW [] [] (ψᵗ ψ₁1 []) [] refl n) (cong ψ₀ᵗ (fs-Ωt n))

nf-ψ₀1 : NF₁ (ψ₀ᵗ (natT 1))
nf-ψ₀1 = n∷ (nψ n[] (sC c[]) nf1 bnd1) n[] tt
  where
  bnd1 : Bnd₁ [] (natT 1)
  bnd1 (vh _) = E.[]<
  bnd1 (vd _ ())
  bnd1 (vs _ ())
  bnd1 (vt ())

nf-n : ∀ n → NF₁ (ψ₀ᵗ (Ωt (Ωᵉ n [])))
nf-n zero = nf-ψ₀1
nf-n (suc n) = NF-Ωᵐ n n[] c[] E.[]<

Ωᵉ< : ∀ n → Ωᵉ n [] <ᵗ Ωᵉ (suc n) []
Ωᵉ< zero = E.[]<
Ωᵉ< (suc n) = E.tl< (Ωᵉ< n)

mono-n : ∀ n → ψ₀ᵗ (Ωt (Ωᵉ n [])) <ᵗ ψ₀ᵗ (Ωt (Ωᵉ (suc n) []))
mono-n n = E.hd< (E.ar< (E.hd< (E.lv< (Ωᵉ< n))))

T₀-label : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tωn 0 ev p) (ψ₀ᵗ (natT 1))
T₀-label = labelᵠ {m = 0} {c = zero} {b = false} (ls {ps = []} {y = 𝟏} {ys = []} refl fl (λ i ()) tt lz) (rs (∼ᶠ-refl Fl) (λ i ()) rz) ok₀ (λ i h r → ok₀ i) nf-ψ₀1
  where
  fl : FlU hon Fl []
  fl (inr ink) = inj₁ z≅

Tn-label : ∀ n {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tωn n ev p) (ψ₀ᵗ (Ωt (Ωᵉ n [])))
Tn-label zero ev p = T₀-label ev p
Tn-label (suc n) ev p = TΩ·-label n ev p

Tω-label : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab₀ (Tω ev p) tω
Tω-label ev p =
  gl (λ n → proj₁ (Tn-label n ev p))
     (λ n → ≺→⊑² (Lab-oc (proj₂ (Tn-label (suc n) ev p)) (nf-n (suc n)) (proj₂ (Tn-label n ev p)) (nf-n n) (mono-n n))) ,
  lω cω-tω (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (fs-tω n)) (proj₂ (Tn-label n ev p)))
```
