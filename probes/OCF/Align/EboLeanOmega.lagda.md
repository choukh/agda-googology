# EboLeanOmega

> **记号侧验收工作**, 读记号, 不进成品. 逐字取自 [WfFsnOmega](WfFsnOmega.lagda.md) (3.3 的 Ω 部分 `NFΩ`, 下标的界 `SB`, 脊上可见性 `G-spine`), 只把导入换成 EboLean 各段; 结论与证明见原文. `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanOmega where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanView
open import OCF.Align.EboLeanTrian

NFΩ : ∀ {a μ} → NF a → (v : VΩ a μ) → ∀ {η} → NF η → η <ᵀ Ωs μ → NF (fΩ v η)
NFΩ n (ωs v) nη p = n∷ (nf-hd n) (hd-lt (nf-le n) (t< (TΩ v p))) (NFΩ (nf-tl n) v nη p)
NFΩ n (ωr e) nη p = nη
NFΩ n (ωl e v) nη p = nf-Ω (NFΩ (nfp-u (nf-hd n)) v nη p)
NFΩ n (ωp {u = u} {μ = μ} be pen v) nη p =
  nf-ψ (nfp-u (nf-hd n)) (NFΩ (nfp-a (nf-hd n)) v nη p)
       (Gtri (TΩ v p) (nfp-g (nf-hd n)) (λ i → ⊥-elim (noG-Ω nη (<-≤ p (Ωs≤ μ u pen)) i)))

-- γ 的首级 Ω_ν 是标准的, 且在 Ω_{ν+1} 之下
nf-W : ∀ {a ν} → NF a → VΩ a ν → NF (Ωt ν)
nf-W n v = nf-Ω (nf-ν n v)

nf-fW : ∀ {a ν} → NF a → (v : VΩ a ν) → NF (fΩ v (Ωt ν))
nf-fW n v = NFΩ n v (nf-W n v) (γ< v zero)

CovZ : T → T → T → Set
CovZ u c x = Cov u c x ⊎ (x ≡ [])

covz-lift : ∀ {u c₀ c x} → (∀ {y} → InG u y c₀ → InG u y c) → CovZ u c₀ x → CovZ u c x
covz-lift f (inj₁ cv) = inj₁ (cov-lift f cv)
covz-lift f (inj₂ e)  = inj₂ e

-- ν ≤ r ≤ ν+1 时 G_u(ν) ⊆ G_u(r): r 只能是 ν 或 ν+1
reg-sub : ∀ {u x ν r A} → sucT ν ≡ A → ν ≤ᵀ r → r ≤ᵀ A → InG u x ν → InG u x r
reg-sub e (inj₂ refl) _ i = i
reg-sub {ν = ν} refl (inj₁ p) (inj₂ refl) i = G-sucT ν i
reg-sub {ν = ν} refl (inj₁ p) (inj₁ q) i with <sucT ν q
... | inj₁ q′   = ⊥-elim (<ᵀ-asym p q′)
... | inj₂ refl = ⊥-elim (<ᵀ-irrefl p)

SB : ∀ {a ν} → NF a → (v : VΩ a ν) → ∀ u c → fΩ v (Ωt ν) ≤ᵀ c → c ≤ᵀ a → ∀ {x} → InG u x ν → CovZ u c x
SB n (ωs {x = x} v) u c (inj₂ refl) r i =
  covz-lift gtl (SB (nf-tl n) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i)
SB n (ωs {x = x} v) u c (inj₁ q) r i with cons-btw q r
... | c₀ , refl , q₀ , r₀ = covz-lift gtl (SB (nf-tl n) v u c₀ (inj₁ q₀) r₀ i)
SB n w@(ωr {u = A} e) u c (inj₂ refl) r i with dec≤ u (pred A)
... | inj₁ m = inj₁ (_ , gp (gw m i) , inj₂ refl)
... | inj₂ p = ⊥-elim (noG-le (nf-ν n w) (inj₁ p) i)
SB n w@(ωr {u = A} e) u c (inj₁ q) r i with dec≤ u (pred A) | psi-sub-btw q r
... | inj₂ p | _ = ⊥-elim (noG-le (nf-ν n w) (inj₁ p) i)
... | inj₁ m | r′ , s , c₁ , refl , l₀ , r₀ =
  inj₁ (_ , gp (gw (≤-trans′ m l₀) (reg-sub (pred-suc A e) l₀ r₀ i)) , inj₂ refl)
SB n (ωl {u = A} {μ = ν} e v) u c (inj₂ refl) r i
  with SB (nfp-u (nf-hd n)) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i
... | inj₂ e′ = inj₂ e′
... | inj₁ (y , j , xy) with dec≤ u (fΩ v (Ωt ν))
...   | inj₁ m = inj₁ (y , gp (gw m j) , xy)
...   | inj₂ p = ⊥-elim (noG-le (nf-fW (nfp-u (nf-hd n)) v) (inj₁ p) j)
SB n (ωl {u = A} {μ = ν} e v) u c (inj₁ q) r i with psi-sub-btw q r
... | r′ , s , c₁ , refl , l₀ , r₀ with dec≤ u r′
...   | inj₁ m = covz-lift (λ j → gp (gw m j)) (SB (nfp-u (nf-hd n)) v u r′ l₀ r₀ i)
...   | inj₂ p with SB (nfp-u (nf-hd n)) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i
...     | inj₂ e′ = inj₂ e′
...     | inj₁ (y , j , xy) = ⊥-elim (noG-le (nf-fW (nfp-u (nf-hd n)) v) (inj₁ (≤-< l₀ p)) j)
SB n w@(ωp {u = A} {μ = ν} be pen v) u c l r i with dec≤ u A
... | inj₂ p = ⊥-elim (noG-le (nf-ν n w) (inj₁ (<-≤ (<-sucT ν) (inj₁ (≤-< (Pen→≤ (sucT ν) A pen) p)))) i)
... | inj₁ m with psi-btw l r
...   | c₀ , c₁ , refl , l₀ , r₀ = covz-lift (λ j → gp (gc m j)) (SB (nfp-a (nf-hd n)) v u c₀ l₀ r₀ i)

G-spine : ∀ {B ν A x} → NF B → VΩ B ν → A ≤ᵀ sucT ν → InG A x (sucT ν) → InG A x B
G-spine n (ωs w) l i = gtl (G-spine (nf-tl n) w l i)
G-spine {A = A} {x} n (ωr {u = u} e) l i =
  gp (gw (subst (A ≤ᵀ_) (pred-suc u e) l) (subst (InG A x) (pred-suc u e) i))
G-spine n (ωl {u = u} e w) l i =
  gp (gw (≤-trans′ l (inj₁ (dom< (nfp-u (nf-hd n)) w))) (G-spine (nfp-u (nf-hd n)) w l i))
G-spine n (ωp {u = u} {μ = ν} be pen w) l i =
  gp (gc (≤-trans′ l (Pen→≤ (sucT ν) u pen)) (G-spine (nfp-a (nf-hd n)) w l i))
```
