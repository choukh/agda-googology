> **机械克隆, 验收用.** 由 `LadderInfWVis` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆, 验收用.** 由 `LadderInfVis` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 读数类的封闭性

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFVis](LadderNFVis.lagda.md) 生成, 下面的说明是原文件的. `VisQ`, `VisQT` 在相似与下移下封闭; `Kl-dom`: 只要 $C'$ 下一切值的层号 $\succeq t+1$, $C'$ 就在 `VisQT t` 里, 这是 "压上一层" 的全部内容. `rdT`, `hoK`: 尾巴压过 $\dot\Omega_t$ 时读出层号. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderLabZInfWVis (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderLabZNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderLabZNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl; addˢ-≅; self-trˢ; self-tr⁻ˢ; tr⁻ˢ-≅; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᴵ→⊑ᴵ)
open import OCF.Align.LadderLabZNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; DemB; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo; ⊑-suc; ⊑L)
open import OCF.Align.LadderLabZNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderLabZNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabZInfWRel 𝕊
open import OCF.Align.LadderLabZInfWCx 𝕊
open import OCF.Align.LadderLabZInfWRules 𝕊
open import OCF.Align.LadderLabZInfWRules2 𝕊
open import OCF.Align.LadderLabZInfWRules3 𝕊
open import OCF.Align.LadderLabZInfWStrict 𝕊
open import OCF.Align.LadderLabZInfWStrict2 𝕊
open import OCF.Align.LadderLabZInfWClass 𝕊
open import OCF.Align.LadderLabZInfWClassF 𝕊 using (NZ-of)
open import OCF.Align.LadderLabZInfWGood 𝕊
```

## §1 下移的搬运

```agda
R-Up : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {y : Q m k φ χ} {y′ : Q m k ψ ρ} → Rq m k k y y′ → Rq m ℓ ℓ (Up r y) (Up r y′)
R-Up zero rr = rob {r = zero} {r′ = zero} (≅ᴵ-refl _) rr (R-ι zero zero rr)
R-Up (self n) rr = rob {r = self n} {r′ = self n} (≅ᴵ-refl _) rr (R-ι (self n) (self n) rr)

Sft-≈ : ∀ {m k b φ χ ψ ρ s} {C : Cx m k φ χ} {C′ : Cx m k ψ ρ} {E : Cx m b Fl (κ Fl)} → C′ ≈ᶜ C → Sft C′ s E → Sft C s E
Sft-≈ o (sB d) = sB (≈ᶜ-trans d o)
Sft-≈ o (sS h) = sS (Sft-≈ (sh-≈ zero o) h)
Sft-≈ o (sL n h) = sL n (Sft-≈ (sh-≈ (self n) o) h)
Sft-≈ o (sT e h) = sT e (Sft-≈ (ptr {e = e} {e′ = e} o) h)
Sft-≈ o (sT⁻ e h) = sT⁻ e (Sft-≈ (ptr⁻ {e = e} {e′ = e} o) h)

-- E 下的值就是 C 下某棵树的值
Sft-lift : ∀ {m k b φ χ s} {C : Cx m k φ χ} {E : Cx m b Fl (κ Fl)} → C ≈ᶜ C → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) → Sft C s E → (w : Q m b Fl (κ Fl)) → Rq m b b w w →
           Σ (Q m k φ χ) λ y → Rq m k k y y × (runᶜ E w ≅ˢ runᶜ C y)
Sft-lift {C = C} o le lc (sB d) w rw = qwk le lc w , rwk rw , runᶜ-≅ d (rwkʳ rw)
Sft-lift {C = C} o le lc (sS h) w rw =
  let L = Sft-lift (sh-≈ zero o) le lc h w rw
  in Up zero (proj₁ L) , R-Up zero (proj₁ (proj₂ L)) , ≅ˢ-trans (proj₂ (proj₂ L)) (up-run zero o (proj₁ (proj₂ L)))
Sft-lift {C = C} o le lc (sL n h) w rw =
  let L = Sft-lift (sh-≈ (self n) o) le lc h w rw
  in Up (self n) (proj₁ L) , R-Up (self n) (proj₁ (proj₂ L)) , ≅ˢ-trans (proj₂ (proj₂ L)) (up-run (self n) o (proj₁ (proj₂ L)))
Sft-lift {C = C} o le lc (sT e h) w rw =
  let L = Sft-lift (ptr {e = e} {e′ = e} o) le lc h w rw
  in trQ e (proj₁ L) , R-trˡ e (R-trʳ e (proj₁ (proj₂ L))) , proj₂ (proj₂ L)
Sft-lift {C = C} o le lc (sT⁻ e h) w rw =
  let L = Sft-lift (ptr⁻ {e = e} {e′ = e} o) le lc h w rw
  in tr⁻Q e (proj₁ L) , R-tr⁻ˡ e (R-tr⁻ʳ e (proj₁ (proj₂ L))) , proj₂ (proj₂ L)

Sft-lvT : ∀ {m k b φ χ} {C : Cx m k φ χ} {E : Cx m b Fl (κ Fl)} → Sft C true E → b ≺ᴵ k
Sft-lvF : ∀ {m k b φ χ} {C : Cx m k φ χ} {E : Cx m b Fl (κ Fl)} → Sft C false E → b ≅ᴵ k
Sft-lvF (sB d) = ≅ᴵ-refl _
Sft-lvF (sT e h) = ≅ᴵ-trans (Sft-lvF h) e
Sft-lvF (sT⁻ e h) = ≅ᴵ-trans (Sft-lvF h) (≅ᴵ-sym e)
Sft-lvT (sS {s = true} h) = ≺-suc (Sft-lvT h)
Sft-lvT (sS {s = false} h) = via (Sft-lvF h) zero
Sft-lvT (sL n h) with Sft-lvT h
... | via e q = via e (lim n q)
Sft-lvT (sT e h) = ≺ᴵ-respʳ (Sft-lvT h) e
Sft-lvT (sT⁻ e h) = ≺ᴵ-respʳ (Sft-lvT h) (≅ᴵ-sym e)

Sft-ss : ∀ {m k b φ χ} s {C : Cx m k φ χ} {E : Cx m b Fl (κ Fl)} → Sft C s E → suc b ⊑ᴵ suc k
Sft-ss true h with Sft-lvT h
... | via e q = s⊑ e (suc q)
Sft-ss false h = s⊑ (Sft-lvF h) zero
```

## §2 封闭性

```agda
VisQ-≈ : ∀ {m k φ χ ψ ρ} {C : Cx m k φ χ} {C′ : Cx m k ψ ρ} → Ctxᶜ C → C ≈ᶜ C′ → VisQ k C′ → VisQ k C
VisQ-≈ c o v = visQ c (λ h G → cpQ v (Sft-≈ o h) G)

VisQT-≈ : ∀ {m k φ χ ψ ρ} {C : Cx m k φ χ} {C′ : Cx m k ψ ρ} → Ctxᶜ C → C ≈ᶜ C′ → VisQT k C′ → VisQT k C
VisQT-≈ c o v = visT (VisQ-≈ c o (vQ v)) (λ h G → tpQ v (Sft-≈ o h) G)

KlT-≈ : ∀ g {m k φ χ ψ ρ} {C : Cx m k φ χ} {C′ : Cx m k ψ ρ} → Ctxᶜ C → C ≈ᶜ C′ → KlT g k C′ → KlT g k C
KlT-≈ g₀ c o v = c
KlT-≈ g₁ c o v = VisQT-≈ c o v
KlT-≈ g₂ c o v = VisQT-≈ c o v

KQ-≈ : ∀ g {m k φ χ ψ ρ} {C : Cx m k φ χ} {C′ : Cx m k ψ ρ} → Ctxᶜ C → C ≈ᶜ C′ → KQ g k C′ → KQ g k C
KQ-≈ g₀ c o v = c
KQ-≈ g₁ c o v = VisQ-≈ c o v
KQ-≈ g₂ c o v = VisQ-≈ c o v

Vis-shq : ∀ {m k φ χ} {C : Cx m (suc k) φ χ} → VisQ (suc k) C → VisQT k (sh zero C)
Vis-shq {C = C} v = visT (visQ (Ctx-sh zero C (cxQ v)) (λ h G → cpQ v (sS h) G)) (λ h G → cpQ v (sS h) G)

Vis-shl : ∀ {m f s φ χ} n {C : Cx m (lim f s) φ χ} → VisQ (lim f s) C → VisQ (f n) (sh (self n) C)
Vis-shl n {C = C} v = visQ (Ctx-sh (self n) C (cxQ v)) (λ h G → cpQ v (sL n h) G)

Kl-ptr : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {C : Cx m b φ χ} → KlT g b C → KlT g a (ptr e C)
Kl-ptr g₀ e v = v
Kl-ptr g₁ e v = visT (visQ (cxQ (vQ v)) (λ h G → cpQ (vQ v) (sT e h) G)) (λ h G → tpQ v (sT e h) G)
Kl-ptr g₂ e v = visT (visQ (cxQ (vQ v)) (λ h G → cpQ (vQ v) (sT e h) G)) (λ h G → tpQ v (sT e h) G)

Kl-ptr⁻ : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {C : Cx m a φ χ} → KlT g a C → KlT g b (ptr⁻ e C)
Kl-ptr⁻ g₀ e v = v
Kl-ptr⁻ g₁ e v = visT (visQ (cxQ (vQ v)) (λ h G → cpQ (vQ v) (sT⁻ e h) G)) (λ h G → tpQ v (sT⁻ e h) G)
Kl-ptr⁻ g₂ e v = visT (visQ (cxQ (vQ v)) (λ h G → cpQ (vQ v) (sT⁻ e h) G)) (λ h G → tpQ v (sT⁻ e h) G)

-- 只要 C′ 下一切值的层号 ⪰ t+1, C′ 就读得出一切下移
Kl-dom : ∀ {m t φ χ} {C′ : Cx m t φ χ} → Ctxᶜ C′ → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) →
         (∀ (y : Q m t φ χ) → Rq m t t y y → (G : Goodᴺ (toZ (runᶜ C′ y))) → suc t ⊑ᴵ lvG G) → VisQT t C′
Kl-dom {m} {t} {C′ = C′} c le lc H =
  visT (visQ c rd) rd
  where
  rd : ∀ {s b} {E : Cx m b Fl (κ Fl)} → Sft C′ s E → (G : Goodᴺ (toZ (runᶜ E (Ω̇ m b)))) → suc b ⊑ᴵ lvG G
  rd {s = s} {b = b} h G =
    let L = Sft-lift (ctxᶜ-refl C′ c) le lc h (Ω̇ m b) (RΩ̇ m (≅ᴵ-refl b))
    in ⊑ᴵ-trans (Sft-ss s h) (pull (proj₂ (proj₂ L)) (H (proj₁ L) (proj₁ (proj₂ L))) G)

rdT : ∀ {m t φ χ} {C : Cx m t φ χ} → VisQT t C → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) → {a : Q m t φ χ} → Ω̇ m t ⊑ᵀ a → (G : Goodᴺ (toZ (runᶜ C a))) → suc t ⊑ᴵ lvG G
rdT {C = C} v le lc h G = ⊑ᴵ-trans (tpQ v (sB o) (proj₁ L)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))
  where
  o = ≈ᶜ-wkˡ le lc (ctxᶜ-refl C (cxQ (vQ v)))
  L = h o G

hoK : ∀ g {m t φ χ} {C : Cx m t φ χ} → KlT g t C → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) → {a : Q m t φ χ} → Ω̇ m t ⊑ᵀ a → Hq g a C
hoK g₀ v le lc h = tt
hoK g₁ v le lc h = tt
hoK g₂ {t = t} v le lc h G = ⊑ᴵ-trans (⊑-suc t) (rdT v le lc h G)

Hq-eag : ∀ g {m c φ χ} {a : Q m c φ χ} {C : Cx m c φ χ} → Hq (eag g) a C
Hq-eag g₀ = tt
Hq-eag g₁ = tt
Hq-eag g₂ = tt

Hq-zero : ∀ g {m φ χ} {a : Q m zero φ χ} {C : Cx m zero φ χ} → Hq g a C
Hq-zero g₀ = tt
Hq-zero g₁ = tt
Hq-zero g₂ G = z⊑

inp-idem : ∀ g → inp (inp g) ≡ inp g
inp-idem g₀ = refl
inp-idem g₁ = refl
inp-idem g₂ = refl

inp-eag : ∀ g → inp (eag g) ≡ inp g
inp-eag g₀ = refl
inp-eag g₁ = refl
inp-eag g₂ = refl
```
