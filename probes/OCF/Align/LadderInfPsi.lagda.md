# 高度抽象: 字面目标的闭包定理

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFPsi](LadderNFPsi.lagda.md) 生成, 下面的说明是原文件的. `PsiM.Psi q : Gq g c 𝓧 x → Gq (inp g) t 𝓖 (ψᵠ q x)`, 对一切 $t<c$, 只要 $C\in\mathcal G$ 推出 `pψ q C` ∈ $\mathcal X$ 且 $C$ 在 `KlT g t`. 与 `OCF.Free.Psi` 行行对应; 档位 $g\ge1$ 时输出 `ι↓` 可读, 类多 `VisQT t`, 由 `KlUp`, `Kl-fl` 沿 "压上一层" 传递. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfPsi (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Free.Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfTree 𝕊
open import OCF.Align.LadderInfRel 𝕊
open import OCF.Align.LadderInfCx 𝕊
open import OCF.Align.LadderInfRules 𝕊
open import OCF.Align.LadderInfRules2 𝕊
open import OCF.Align.LadderInfRules3 𝕊
open import OCF.Align.LadderInfStrict 𝕊
open import OCF.Align.LadderInfStrict2 𝕊
open import OCF.Align.LadderInfClass 𝕊
open import OCF.Align.LadderInfClassF 𝕊 using (inp-map)
open import OCF.Align.LadderInfGood 𝕊
open import OCF.Align.LadderInfVis 𝕊
open import OCF.Align.LadderInfIota 𝕊
open import OCF.Align.LadderInfAdd 𝕊
open import OCF.Align.LadderInfTr 𝕊
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open RestrQ
```

## §1 辅助

```agda
demFl : ∀ {K X φ} (q : InF K (Fl ⊔ φ)) → (∀ {K′} (k : InF K′ φ) → Dem X k) → Dem X q
demFl (inl (inr ink)) h = inj₂ z≅
demFl (inr k) h = h k

DmZ : ∀ {m X φ χ} → Dm m X φ χ → Dm m X (Fl ⊔ φ) (Z* χ)
DmZ d = (λ q → demFl q (proj₁ d)) , (λ i r q → demFl q (proj₂ d i r))

K-inp : ∀ g {m k φ χ} {D : Cx m k φ χ} → KlT g k D → KlT (inp g) k D
K-inp g₀ v = v
K-inp g₁ v = v
K-inp g₂ v = v

K→Q : ∀ g {m k φ χ} {D : Cx m k φ χ} → KlT g k D → KQ (inp g) k D
K→Q g₀ v = v
K→Q g₁ v = vQ v
K→Q g₂ v = vQ v

Kl-wk : ∀ g {m k φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {D : Cx m k ψ ρ} → KlT g k D → KlT g k (wkC le lc D)
Kl-wk g {le = le} {lc = lc} {D = D} v = KlT-≈ g (Ctx-wkC D (KlT→Ctx g v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl D (KlT→Ctx g v))) v

KQ-wk : ∀ g {m k φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {D : Cx m k ψ ρ} → KQ g k D → KQ g k (wkC le lc D)
KQ-wk g {le = le} {lc = lc} {D = D} v = KQ-≈ g (Ctx-wkC D (KQ→Ctx g v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl D (KQ→Ctx g v))) v

rdK : ∀ {m t φ χ ψ ρ} {C : Cx m t φ χ} {C′ : Cx m t ψ ρ} → VisQT t C → C′ ≈ᶜ C → (le : ∀ {L} → Ev L ψ → Ev L Fl) (lc : Sub m ρ (κ Fl)) → {a : Q m t ψ ρ} → Ω̇ m t ⊑ᵀ a → (G : Goodᴺ (toZ (runᶜ C′ a))) → suc t ⊑ᴵ lvG G
rdK {C′ = C′} v o le lc h G = ⊑ᴵ-trans (tpQ v (sB (≈ᶜ-trans (≈ᶜ-wkˡ le lc (≈ᶜ-reflˡ o)) o)) (proj₁ L)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))
  where
  L = h (≈ᶜ-wkˡ le lc (≈ᶜ-reflˡ o)) G

-- 压上一层: C′ 下的值就是 D 下某个 ⊒ Ω̇_t 的值
KlUp : ∀ g {m t φ χ ψ ρ} {D : Cx m t φ χ} {C′ : Cx m t ψ ρ} → Ctxᶜ C′ → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) (le′ : ∀ {L} → Ev L ψ → Ev L Fl) (lc′ : Sub m ρ (κ Fl)) →
       (∀ (y : Q m t ψ ρ) → Rq m t t y y → Σ (Q m t φ χ) λ a → (Ω̇ m t ⊑ᵀ a) × (runᶜ C′ y ≅ˢ runᶜ D a)) → KlT g t D → KlT g t C′
KlUp g₀ c le lc le′ lc′ H v = c
KlUp g₁ {D = D} c le lc le′ lc′ H v = Kl-dom c le′ lc′ (λ y ry G → let L = H y ry in pull (proj₂ (proj₂ L)) (rdT v le lc (proj₁ (proj₂ L))) G)
KlUp g₂ {D = D} c le lc le′ lc′ H v = Kl-dom c le′ lc′ (λ y ry G → let L = H y ry in pull (proj₂ (proj₂ L)) (rdT v le lc (proj₁ (proj₂ L))) G)

Kl-fl : ∀ g {m t φ χ} {O₁ C″ : Cx m t φ χ} {a : Q m t φ χ} → (le : ∀ {L} → Ev L φ → Ev L Fl) (lc : Sub m χ (κ Fl)) → Ω̇ m t ⊑ᵀ a → KlT g t O₁ → FlOverᵀ a O₁ C″ → KlT g t C″
Kl-fl g₀ le lc h v f = cxoᵀ f
Kl-fl g₁ le lc h v f = Kl-dom (cxoᵀ f) le lc (λ y ry G → let L = flwᵀ f y ry G in ⊑ᴵ-trans (rdT v le lc h (proj₁ L)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)))
Kl-fl g₂ le lc h v f = Kl-dom (cxoᵀ f) le lc (λ y ry G → let L = flwᵀ f y ry G in ⊑ᴵ-trans (rdT v le lc h (proj₁ L)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)))

Kl-un : ∀ g₁ {m t ξ ζ} {D₁ : Cx m t ξ ζ} → KlT (inp g₁) t D₁ → KlT g₁ t D₁
Kl-un g₀ v₁ = v₁
Kl-un g₁ v₁ = v₁
Kl-un g₂ v₁ = v₁
```

## §2 `Psi`

```agda
module PsiM (Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)) where
  Psi : ∀ {g m c t φ χ} (q : t <ᴵ c) {𝓖 : ClT m t (Fl ⊔ φ) (Z* χ)} {𝓧 : ClT m c φ χ} {x : Q m c φ χ} → (∀ {C} → 𝓖 C → 𝓧 (pψ q C)) → (∀ {C} → 𝓖 C → KlT g t C) → Gq g m c 𝓧 x → Gq (inp g) m t 𝓖 (ψᵠ q x)
  PsiPen : ∀ {g m c t φ χ k k′} (q : t <ᴵ c) {𝓖 : ClT m t (Fl ⊔ φ) (Z* χ)} {𝓧 : ClT m c φ χ} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} →
         (∀ {C} → 𝓖 C → 𝓧 (pψ q C)) → (∀ {C} → 𝓖 C → KlT g t C) →
         (𝓖₀ : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓧 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ ζ C′) →
         (W : ∀ ξ ζ → Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ) → Cx m k ξ ζ) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → ∀ (u : Q m k ξ ζ) → Rq m k k u u → runᶜ (W ξ ζ C) u ≅ˢ runᶜ C (h ξ ζ (intoU (<→◃ r) u))) →
         (∀ (𝓔 : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → 𝓖₀ ξ ζ C) → ∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → LG m c (inp g) (<→◃ r) (W ξ ζ ⟪ 𝓔 ξ ζ ⟫ᵀ) z → Gq g m c (𝓔 ξ ζ) (h ξ ζ (intoU (<→◃ r) z))) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → KlT g k (W ξ ζ C)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓖₀ ξ ζ C → AboveΩ C′ (W ξ ζ C) → NdG g C′ → 𝓖₀ ξ ζ C′) →
         (∀ ξ ξ′ ζ ζ′ {C : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} {C′ : Cx m c (ξ′ ⊔ φ) (lo m ζ′ ∪ χ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ ζ′ C′ → 𝓖₀ ξ ζ C) →
         (∀ {ξ ξ′ ζ ζ′} {z : Q m k ξ ζ} {z′ : Q m k ξ′ ζ′} → z ⊑ᵗ z′ → h ξ ζ (intoU (<→◃ r) z) ⊑ᵗ h ξ′ ζ′ (intoU (<→◃ r) z′)) →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k ξ′ ζ′) → Rq m k k z z′ → Rq m c c (h ξ ζ (intoU (<→◃ r) z)) (h ξ′ ζ′ (intoU (<→◃ r) z′))) →
         (e : k ≅ᴵ k′) (s : k′ <ᴵ t) → Gq (inp g) m t 𝓖 (qΩ proj₁ s (λ ξ ζ y → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e (outU (<→◃ s) y)))))))
  PsiCh : ∀ {g m c t φ χ k} (q : t <ᴵ c) {𝓖 : ClT m t (Fl ⊔ φ) (Z* χ)} {𝓧 : ClT m c φ χ} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} →
         (∀ {C} → 𝓖 C → 𝓧 (pψ q C)) → (∀ {C} → 𝓖 C → KlT g t C) →
         (𝓖₀ : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓧 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ ζ C′) →
         (W : ∀ ξ ζ → Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ) → Cx m k ξ ζ) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → ∀ (u : Q m k ξ ζ) → Rq m k k u u → runᶜ (W ξ ζ C) u ≅ˢ runᶜ C (h ξ ζ (intoU (<→◃ r) u))) →
         (∀ (𝓔 : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → 𝓖₀ ξ ζ C) → ∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → LG m c (inp g) (<→◃ r) (W ξ ζ ⟪ 𝓔 ξ ζ ⟫ᵀ) z → Gq g m c (𝓔 ξ ζ) (h ξ ζ (intoU (<→◃ r) z))) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → KlT g k (W ξ ζ C)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓖₀ ξ ζ C → AboveΩ C′ (W ξ ζ C) → NdG g C′ → 𝓖₀ ξ ζ C′) →
         (∀ ξ ξ′ ζ ζ′ {C : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} {C′ : Cx m c (ξ′ ⊔ φ) (lo m ζ′ ∪ χ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ ζ′ C′ → 𝓖₀ ξ ζ C) →
         (∀ {ξ ξ′ ζ ζ′} {z : Q m k ξ ζ} {z′ : Q m k ξ′ ζ′} → z ⊑ᵗ z′ → h ξ ζ (intoU (<→◃ r) z) ⊑ᵗ h ξ′ ζ′ (intoU (<→◃ r) z′)) →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k ξ′ ζ′) → Rq m k k z z′ → Rq m c c (h ξ ζ (intoU (<→◃ r) z)) (h ξ′ ζ′ (intoU (<→◃ r) z′))) →
         Gq (inp g) m t 𝓖 (ql (λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n))))))

  Psi {g} {m} {t = t} q H H₂ g0 = gw (KQ (inp g) t) (λ {C} c → K→Q g (Kl-wk g {le = proj₁} {lc = fc*} (H₂ c))) (Ω̇G g m t)
  Psi {g} {m} {c = c} {t = t} {φ = φ} {χ = χ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gs {a = a} 𝓚 v k clk cgk ho hq) =
    gl (λ n → Gmono (λ c₁ → H₂ c₁ , v (H c₁)) (rep-good n)) mono
    where
    𝓐 : ClT m t (Fl ⊔ φ) (Z* χ)
    𝓐 C = KlT g t C × 𝓚 (pψ q C)
    X = ψᵠ q a
    gX : Gq (inp g) m t 𝓐 X
    gX = Psi q proj₂ proj₁ k
    ra = G→R k
    rX : Rq m t t X X
    rX = R-ψᵠ q q (≅ᴵ-refl _) ra
    Xfl : ∀ n → X ⊑ᵀ repᵠ X (suc n)
    Xfl zero = R→⊑ᵀ rX
    Xfl (suc n) = wk-rᵀ (B1ᵀ rX (Xfl n))
    rR : ∀ n → Rq m t t (repᵠ X n) (repᵠ X n)
    rR n = R-repᵠ (∼ᶠ-refl _) (Sim∼-refl _) rX n
    ΩX : Ω̇ m t ⊑ᵀ X
    ΩX = P0ᵀ {q = q} ra (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl t)))
    ΩR : ∀ n → Ω̇ m t ⊑ᵀ repᵠ X (suc n)
    ΩR n = ⊑ᵀ-trans ΩX (Xfl n)
    wf : ∀ n → WFl (repᵠ X (suc n))
    wf n = wfl (rR (suc n)) (⊑ᵀ-trans (P0ᵀ {q = q} ra (𝟏⊑Ω̇ m t)) (Xfl n))
    clA : ∀ n {O₁ C″} → 𝓐 O₁ → FlOverᵀ (repᵠ X (suc n)) O₁ C″ → 𝓐 C″
    clA n {O₁} {C″} (x , c₁) f = Kl-fl g proj₁ fc* (ΩR n) x f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t₁ rt G →
      let L = flwᵀ f (ψᵠ q t₁) (R-ψᵠ q q (≅ᴵ-refl _) rt) G
          N = Xfl n (ctxᶜ-refl O₁ (KlT→Ctx g x)) (proj₁ L)
      in proj₁ N , ⊑-trans (proj₂ N) (proj₂ L))) (ndg _ tt)
    hoA : ∀ n {C} → 𝓐 C → HonT (repᵠ X (suc n)) C
    hoA n {C} (x , c₁) G =
      let N = Xfl n (ctxᶜ-refl C (KlT→Ctx g x)) G
          U = toLevel-⊑ (forceᴺ-HS _ (proj₁ N)) (forceᴺ-HS _ G) (proj₂ N)
      in DmZ ((λ k₁ → demUp k₁ U (proj₁ (ho c₁ (proj₁ N)) k₁)) , (λ i r k₁ → demUp k₁ U (proj₂ (ho c₁ (proj₁ N)) i r k₁)))
    press : ∀ n {C} → 𝓐 C → 𝓐 (pa (repᵠ X (suc n)) (wkC (λ e → e , e) (λ i r e → e , e) C))
    press n {C} (x , c₁) = KlUp g {D = C} (wf n , Ctx-wkC C (KlT→Ctx g x)) proj₁ fc* proj₁ fc*
        (λ y ry → qwk (λ e → e , e) (λ i r e → e , e) (repᵠ X (suc n) ⊞ y) , wk-rᵀ (B1ᵀ ry (ΩR n)) , subst (λ w → runᶜ (wkC (λ e → e , e) (λ i r e → e , e) C) (repᵠ X (suc n) ⊞ y) ≅ˢ w) (run-wkC (λ e → e , e) (λ i r e → e , e) C (repᵠ X (suc n) ⊞ y)) (runᶜ-≅ (≈ᶜ-reflʳ (≈ᶜ-wkʳ (λ e → e , e) (λ i r e → e , e) (ctxᶜ-refl C (KlT→Ctx g x)))) (R-⊞ (∼ᶠ-refl _) (Sim∼-refl _) (rR (suc n)) ry))) x ,
      clk c₁ (flo-overᵀ (wf n , Ctx-wkC C (KlT→Ctx g x)) (λ t₁ rt G →
      B1ᵀ {x = X} {W = repᵠ X (suc n)} (R-ψᵠ q q (≅ᴵ-refl _) rt) (Xfl n) (≈ᶜ-wkʳ (λ e → e , e) (λ i r e → e , e) (ctxᶜ-refl C (KlT→Ctx g x))) G)) (ndg _ tt)
    dup-𝓐 : ∀ {C : Cx m t (Fl ⊔ φ) (Z* χ)} → 𝓐 C → 𝓐 (wkC proj₁ pr₁ᶜ (wkC (λ e → e , e) (λ i r e → e , e) C))
    dup-𝓐 {C} (x , c₁) =
      let cc = KlT→Ctx g x
          oo = ≈ᶜ-wkˡ proj₁ pr₁ᶜ (≈ᶜ-wkˡ (λ e → e , e) (λ i r e → e , e) (ctxᶜ-refl C cc))
          c₂ = Ctx-wkC (wkC (λ e → e , e) (λ i r e → e , e) C) (Ctx-wkC C cc)
      in KlT-≈ g c₂ oo x , cgk c₂ (pψ oo) c₁
    rep-good : ∀ n → Gq (inp g) m t 𝓐 (repᵠ X n)
    rep-good zero = g0
    rep-good (suc zero) = gX
    rep-good (suc (suc n)) =
      gw (λ E → 𝓐 (wkC proj₁ pr₁ᶜ E) × 𝓐 (pa (repᵠ X (suc n)) E))
         (λ {C} c₁ → dup-𝓐 c₁ , press n c₁)
         (AddT.Add {W = repᵠ X (suc n)} (rep-good (suc n)) (wf n)
                   (λ x o (y , c₁) → KlT-≈ g x o y , cgk x (pψ o) c₁) (clA n) (λ c₁ → KlT→Ctx g (proj₁ c₁)) (hoA n) (λ c₁ → hoK (inp g) (K-inp g (proj₁ c₁)) proj₁ fc* (ΩR n))
                   {g′ = inp g} (inp-idem g) {𝓐₁ = λ E → 𝓐 (wkC proj₁ pr₁ᶜ E) × 𝓐 (pa (repᵠ X (suc n)) E)} {𝓧 = 𝓐} proj₁ proj₂ gX)
    mono : ∀ n → repᵠ X n ⊑ᵗ repᵠ X (suc n)
    mono zero = ⊑ᵀ→ᵗ rz (zero-lᵀ rX)
    mono (suc n) = wk-rᵗ (⊑ᵀ→ᵗ (rR (suc n)) (B1ᵀ rX (R→⊑ᵀ (rR (suc n)))))
  Psi q H H₂ (gl f st) = gl (λ n → Psi q H H₂ (f n)) (λ n → ψ-congᵗ {q = q} (st n))
  Psi {g} {φ = φ} {χ = χ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gi {j = j} {f = f} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gi (λ D → KlT g _ D × 𝓖₀ (pψ q D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W₀ (pψ q D)) (λ (x , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez gz → Psi q {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pψ q D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
          (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pψ q D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) gz)))
       (λ (x , c₀) → Wv c₀)
       (λ {D} {C′} (x , c₀) (aboveV cx′ wrap) nd →
          KlUp g {D = D} cx′ proj₁ fc* proj₁ fc* (λ y ry →
            let Wp = wrap y ry
                u = proj₁ Wp
                eu = proj₁ (proj₂ Wp)
            in ψᵠ q (f u) , P0ᵀ {q = q} (rf eu) (R→⊑ᵀ (RΩ̇ _ (≅ᴵ-refl _))) , ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf c₀ u eu)) x ,
          St c₀ (aboveV cx′ (λ t₁ rt → wrap (ψᵠ q t₁) (R-ψᵠ q q (≅ᴵ-refl _) rt))) (ndg _ tt))
       (λ x o (y , c₀) → KlT-≈ g x o y , cg x (pψ o) c₀)
       (λ h → ψ-congᵗ {q = q} (hm h)) (λ d → R-ψᵠ q q (≅ᴵ-refl _) (rf d))
  Psi q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pψ q D)) Bc (Psi q H H₂ g₀′)
       (λ η e → Psi q {𝓖 = λ D → 𝓖 D × 𝓑 η (pψ q D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
       (R-ψᵠ q q (≅ᴵ-refl _) et) (λ η e η′ e′ d → R-ψᵠ q q (≅ᴵ-refl _) (eg η e η′ e′ d)) (λ η e → ψ-congᵗ {q = q} (m₁ η e)) (λ η e η′ e′ u → ψ-congᵗ {q = q} (mm η e η′ e′ u))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Psi q H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-ψᵠ q q (≅ᴵ-refl _) r₁) (λ η e η′ e′ d → R-ψᵠ q q (≅ᴵ-refl _) (r₂ η e η′ e′ d)) (Psi q H H₂ go) (λ k → Psi q H H₂ (gO k)) (ψ-congᵗ {q = q} mo) (λ k → ψ-congᵗ {q = q} (mO k))
  Psi {g} q H H₂ (gw {le = le} {lc = lc} 𝓖₁ inc₁ k) =
    gw (λ E → KlT g _ E × 𝓖₁ (pψ q E)) (λ {C} c → Kl-wk g (H₂ c) , inc₁ (H c)) (Psi q proj₂ proj₁ k)
  Psi {g} {m} {t = t} {φ = φ₀ ⊔ fk zero} {χ = χ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gclo {φ = φ₀} {t = t₀} {h = g₁′} 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gw (𝓖ₐ 𝓖ᵗ) (λ {C} c₁ →
           let cc = KlT→Ctx g (H₂ c₁)
               o₁ = ≈ᶜ-wkˡ asr sub-id (≈ᶜ-wkˡ asl sub-id (ctxᶜ-refl C cc))
           in Kl-wk g (H₂ c₁) , cgᵗ (Ctx-wkC (wkC asl sub-id C) (Ctx-wkC C cc)) (pψ o₁) (inc₁ (H c₁)))
       (gclo (𝓖ₐ 𝓖ᵗ) (λ c₁ → c₁)
         (λ {C} {C′} x o (y , c₁) → KlT-≈ g x o y , cgᵗ (Ctx-wkC C′ x) (pψ (wk≈ asr sub-id asr sub-id o)) c₁)
         (λ η → 𝓖ₐ (𝓖ᵍ η))
         (λ {η} {η′} {C} {C′} e x o (y , c₁) → KlT-≈ g x o y , Bc e (Ctx-wkC C′ x) (pψ (wk≈ asr sub-id asr sub-id o)) c₁)
         (gw (𝓖₂ 𝓖ᵗ) (λ {D} (x , c₁) → Kl-wk g x , c₁) (Psi q proj₂ proj₁ gt))
         (λ η → gw (𝓖₂ (𝓖ᵍ η)) (λ {D} (x , c₁) → Kl-wk g x , c₁) (Psi q proj₂ proj₁ (gg η)))
         (rwk (R-ψᵠ q q (≅ᴵ-refl _) rt)) (λ η η′ d → rwk (R-ψᵠ q q (≅ᴵ-refl _) (rg η η′ d)))
         (λ η h → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (m₁ η h)))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (mm η η′ h u))))
         (λ {D} (_ , c₁) → at≡ (run-wkC asr sub-id D (ψᵠ q t₀)) {P = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dt c₁ G₁)))
         (λ η {D} (_ , c₁) → at≡ (run-wkC asr sub-id D (ψᵠ q (g₁′ η))) {P = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dg η c₁ G₁)))
         (λ {D} (x₀ , c₁) → at≡ (run-wkC asr sub-id D (ψᵠ q t₀)) {P = λ X → ∀ {C′ : Cx m t ((Fl ⊔ φ₀) ⊔ fk X) (Z* χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → KlT-≈ g x o x₀ , ch₀ c₁ G₁ (Ctx-wkC C′ x) (pψ (wk≈ asr sub-id asr sub-id o))))
         (λ η {D} (x₀ , c₁) → at≡ (run-wkC asr sub-id D (ψᵠ q (g₁′ η))) {P = λ X → ∀ {C′ : Cx m t ((Fl ⊔ φ₀) ⊔ fk X) (Z* χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → KlT-≈ g x o x₀ , chS η c₁ G₁ (Ctx-wkC C′ x) (pψ (wk≈ asr sub-id asr sub-id o)))))
    where
    𝓖ₐ : ∀ {η} → ClT m _ (φ₀ ⊔ fk η) χ → ClT m t ((Fl ⊔ φ₀) ⊔ fk η) (Z* χ)
    𝓖ₐ 𝓖′ D = KlT g t D × 𝓖′ (pψ q (wkC asr sub-id D))
    𝓖₂ : ∀ {η} → ClT m _ (φ₀ ⊔ fk η) χ → ClT m t (Fl ⊔ (φ₀ ⊔ fk η)) (Z* χ)
    𝓖₂ 𝓖′ E = KlT g t E × 𝓖′ (pψ q E)
  Psi {g} {m} {t = t} {φ = φ} {χ = χ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gcl {n = n} {ψ = ψ} {t = t₀} {h = g₁′} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gcl {ψ = Fl ⊔ ψ} (λ D → KlT g t D × 𝓖ᵗ (pψ q D)) (λ c → H₂ c , inc₁ (H c)) 𝓖ₚ
       (λ {η} {η′} {C} {C′} e x o (y , c₁) → KlT-≈ g x o y , Bc e (Ctx-wkC C′ x) (pψ (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) o)) c₁)
       (Psi q proj₂ proj₁ gt)
       (λ η → gw (λ D → KlT g t D × 𝓖ᵍ η (pψ q D)) (λ {D} (x , c₁) → Kl-wk g x , c₁) (Psi q proj₂ proj₁ (gg η)))
       (R-ψᵠ q q (≅ᴵ-refl _) rt) (λ η η′ d → rwk (R-ψᵠ q q (≅ᴵ-refl _) (rg η η′ d)))
       (λ η h → wk-rᵗ (ψ-congᵗ {q = q} (m₁ η h))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (mm η η′ h u))))
       (λ (_ , c₁) G₁ r₁ → demFl r₁ (dt c₁ G₁))
       (λ η {D} (_ , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (ψᵠ q (g₁′ η))) {P = λ X → ∀ {K} (r₁ : InF K (Fl ⊔ ψ)) → Dem X r₁} (λ G₁ r₁ → demFl r₁ (dg η c₁ G₁)))
       (λ {D} (x₀ , c₁) G₁ {C′} x o → KlT-≈ g x o x₀ , ch₀ c₁ G₁ (Ctx-wkC C′ x) (pψ (≈ᶜ-wkˡ (λ u → u) (AU _) o)))
       (λ η {D} (x₀ , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (ψᵠ q (g₁′ η))) {P = λ X → ∀ {C′ : Cx m t (Fl ⊔ φ) (upd (Z* χ) n ((Fl ⊔ ψ) ⊔ fk X))} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₚ X C′}
           (λ G₁ {C′} x o → KlT-≈ g x o x₀ , chS η c₁ G₁ (Ctx-wkC C′ x) (pψ (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) o))))
    where
    AU : ∀ η → Sub m (upd (κ Fl ∪ χ) n ((Fl ⊔ ψ) ⊔ fk η)) (κ Fl ∪ upd χ n (ψ ⊔ fk η))
    AU η = ⇑ (as-upd {κ Fl} {χ} n η)
    𝓖ₚ : ∀ η → ClT m t (Fl ⊔ φ) (upd (κ Fl ∪ χ) n ((Fl ⊔ ψ) ⊔ fk η))
    𝓖ₚ η D = KlT g t D × 𝓖ᵍ η (pψ q (wkC (λ u → u) (AU η) D))
  Psi {g} {m} {t = t} {φ = φ} {χ = χ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ↓ {n = n} {k = k₁} {q = q₁} {h = h₀} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gΩ↓ 𝓖₀′
       (λ ξ ζ {C} {C′} c₁ x o → KlT-≈ g x o (H₂ c₁) , inc₀ ξ ζ (H c₁) (Ctx-wkC C′ x) (pψ (≈ᶜ-wkˡ swp (λ i r′ → swp) o)))
       (λ ξ ζ D → W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D)))
       (λ ξ ζ {D} (x , c₀) u ru → subst (λ v → runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (ψᵠ q (h₀ ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru))
       (λ 𝓔′ inc″ ξ ζ z rz gz →
          gw (𝓖₅ 𝓔′ ξ ζ) (λ {D} c₁ → Kl-wk g (proj₁ (inc″ ξ ζ c₁)) , (D , c₁ , refl))
              (Psi q proj₂ proj₁ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ z rz
                 (intoGV q₁ (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV q₁ gz))))))
       (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) nd →
          KlUp g {D = D} cx′ (λ e → proj₁ (proj₂ e)) lc₃ (λ e → proj₁ (proj₂ e)) lc₃ (λ y ry →
             let Wp = wrap y ry
                 u = proj₁ Wp
                 ru = proj₁ (proj₂ Wp)
             in qwk swp (λ i r′ → swp) (ψᵠ q (h₀ ξ ζ (intoV q₁ u))) , wk-rᵀ (P0ᵀ {q = q} (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) u u ru) (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl t)))) ,
                ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (subst (λ v → runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (ψᵠ q (h₀ ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru))) x ,
          St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t₁ rt →
          let Wp = wrap (qwk swp (λ i r′ → swp) (ψᵠ q t₁)) (rwk (R-ψᵠ q q (≅ᴵ-refl _) rt))
          in proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) (proj₁ Wp)) (sym (run-wkC swp (λ i r′ → swp) C′ (ψᵠ q t₁))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (y , c₀) → KlT-≈ g x o y , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pψ (wk≈ swp (λ i r′ → swp) swp (λ i r′ → swp) o)) c₀)
       (λ u → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (hm u))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ψᵠ q q (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    where
    lc₃ : ∀ {ζ} → Sub m (lo n ζ ∪ Z* χ) (κ Fl)
    lc₃ i r e = proj₁ (proj₂ e)
    𝓖₀′ : ∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)
    𝓖₀′ ξ ζ D = KlT g t D × 𝓖₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo n ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pψ q (wkC swp (λ i r′ → swp) D))
    𝓖₅ : (∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m t (Fl ⊔ (ξ ⊔ φ)) (Z* (lo n ζ ∪ χ))
    𝓖₅ 𝓔′ ξ ζ E = KlT g t E × 𝓧₃ 𝓔′ ξ ζ (pψ q E)
  Psi {φ = φ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ {k = k₁} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) with <ᴵ-dec r q
  ... | injᵃ (via e s) = PsiPen q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf e s
  ... | injᵇ _ = PsiCh q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf
  ... | injᶜ _ = PsiCh q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf
  Psi {g} {m} {t = t} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gm zc rz₁ gx) =
    subst (λ g′ → Gq g′ m t 𝓖 _) (inp-eag g) (Psi {g = eag g} q {𝓖 = 𝓖} {𝓧 = λ C → 𝓧 C × Nd C} (λ c → H c , tt) (λ c → Kl-eag g (H₂ c)) gx)
  PsiPen {g} {m} {c = c} {t = t} {φ = φ} {χ = χ} {k = k₁} {k′ = k′} q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf e s =
    gΩ 𝓖₀′
       (λ ξ ζ {C} {C′} c₁ x o → KlT-≈ (inp g) x o (K-inp g (H₂ c₁)) , inc₀ ξ ζ (H c₁) (Ctx-wkC C′ x) (pψ (≈ᶜ-wkˡ swp (λ i r′ → swp) o)))
       (λ ξ ζ D → ptr⁻ e (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))))
       (λ ξ ζ {D} (x , c₀) u ru →
          subst (λ v → runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) (tr⁻Q e u) ≅ˢ runᶜ D (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e v)))))) (sym (out-intoU (<→◃ s) u))
                (subst (λ v → runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) (tr⁻Q e u) ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e u))))) (Wf ξ ζ c₀ (tr⁻Q e u) (R-tr⁻₂ e e ru))))
       (λ 𝓔′ inc″ ξ ζ z rz gz →
          subst (λ v → Gq (inp g) m t (𝓔′ ξ ζ) (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e v)))))) (sym (out-intoU (<→◃ s) z))
          (gw (𝓖₅ 𝓔′ ξ ζ) (λ {D} c₁ → Kl-wk g (Kl-back (proj₁ (inc″ ξ ζ c₁))) , (D , c₁ , refl))
              (Psi q proj₂ proj₁ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ (tr⁻Q e z) (R-tr⁻₂ e e rz)
                 (intoG (<→◃ r) (Tr⁻ᵀ e {𝓧 = (λ D → ptr⁻ e (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D)))) ⟪ 𝓔′ ξ ζ ⟫ᵀ} (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , ptr⁻ o }) proj₁ (subst (λ g′ → Gq g′ m k′ _ z) (inp-idem g) (outG (<→◃ s) gz))))))))
       (λ ξ ζ (x , c₀) → Kl-ptr⁻ (inp g) e (K-inp g (Wv ξ ζ c₀)))
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) nd →
          KlUp (inp g) {D = D} cx′ (λ u → proj₁ (proj₂ u)) lc₃ (λ u → proj₁ (proj₂ u)) lc₃ (λ y ry →
             let Wp = wrap y ry
                 u = proj₁ Wp
                 ru = proj₁ (proj₂ Wp)
             in qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e u)))) , wk-rᵀ (P0ᵀ {q = q} (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ (R-tr⁻₂ e e ru)) (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl t)))) ,
                ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (subst (λ v → runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) (tr⁻Q e u) ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e u))))) (Wf ξ ζ c₀ (tr⁻Q e u) (R-tr⁻₂ e e ru)))) x ,
          St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t₁ rt →
          let Wp = wrap (qwk swp (λ i r′ → swp) (ψᵠ q t₁)) (rwk (R-ψᵠ q q (≅ᴵ-refl _) rt))
          in tr⁻Q e (proj₁ Wp) , R-tr⁻₂ e e (proj₁ (proj₂ Wp)) , FlΩ̇-tr⁻ e (proj₁ (proj₂ (proj₂ Wp))) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))) (tr⁻Q e (proj₁ Wp))) (sym (run-wkC swp (λ i r′ → swp) C′ (ψᵠ q t₁))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (y , c₀) → KlT-≈ (inp g) x o y , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pψ (wk≈ swp (λ i r′ → swp) swp (λ i r′ → swp) o)) c₀)
       (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e v)))) ⊑ᵗ qwk swp (λ i r′ → swp) (ψᵠ q (h ξ′ ζ′ (intoU (<→◃ r) (tr⁻Q e v′))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
          (wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (hm (tr⁻ᵗ-cong {e = e} {e′ = e} u))))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ v v′ → Rq m t t (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e v))))) (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ′ ζ′ (intoU (<→◃ r) (tr⁻Q e v′)))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
          (rwk (R-ψᵠ q q (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻₂ e e l)))))
    where
    lc₃ : ∀ {ζ} → Sub m (lo m ζ ∪ Z* χ) (κ Fl)
    lc₃ i r′ u = proj₁ (proj₂ u)
    Kl-back : ∀ {ξ ζ} {D : Cx m t ξ ζ} → KlT (inp g) t D → KlT g t D
    Kl-back {D = D} v = Kl-un g v
    𝓖₀′ : ∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo m ζ ∪ Z* χ)
    𝓖₀′ ξ ζ D = KlT (inp g) t D × 𝓖₀ ξ ζ (pψ q (wkC swp (λ i r′ → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo m ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pψ q (wkC swp (λ i r′ → swp) D))
    𝓖₅ : (∀ ξ ζ → ClT m t (ξ ⊔ (Fl ⊔ φ)) (lo m ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m t (Fl ⊔ (ξ ⊔ φ)) (Z* (lo m ζ ∪ χ))
    𝓖₅ 𝓔′ ξ ζ E = KlT g t E × 𝓧₃ 𝓔′ ξ ζ (pψ q E)
  PsiCh {g} {m} {c = c} {t = t} {φ = φ} {χ = χ} {k = k₁} q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf =
    gl (λ n → gw 𝓖₇ (λ {C} c₁ → Kl-wk g {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* m)} (H₂ c₁) , inc₀ ξ* Z₁ (H c₁) (Ctx-wkC C (KlT→Ctx g (H₂ c₁))) (pψ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (⇑ (cv* m)) (ctxᶜ-refl C (KlT→Ctx g (H₂ c₁))))))
                 (Psi q {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt n) (G→R (zG n)) (intoG (<→◃ r) (zG n)))))
       (λ n → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (hm (zm n)))))
    where
    ξ* = Fl ⊔ φ
    Z₁ = Z* χ
    f : Q m k₁ ξ* Z₁ → Q m k₁ ξ* Z₁
    f z = qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h ξ* Z₁ (intoU (<→◃ r) z)))
    zt : ℕ → Q m k₁ ξ* Z₁
    zt = chainᵠ proj₁ fc* f
    𝓖₆ : ClT m k₁ (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo m Z₁ ∪ χ))
    𝓖₆ E = KlT g k₁ E × 𝓖₀ ξ* Z₁ (pψ r E)
    𝓖₇ : ClT m t (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo m Z₁ ∪ χ))
    𝓖₇ E = KlT g t E × 𝓖₀ ξ* Z₁ (pψ q E)
    zG : ∀ n → Gq (inp g) m k₁ (W₀ ξ* Z₁ ⟪ 𝓖₀ ξ* Z₁ ⟫ᵀ) (zt n)
    zG zero = gw (KQ (inp g) k₁) (λ {D} (x , C , c₁ , o) → K→Q g (Kl-wk g {le = proj₁} {lc = fc*} (KlT-≈ g x o (Wv ξ* Z₁ c₁)))) (Ω̇G g m k₁)
    zG (suc n) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk g {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* m)} (KlT-≈ g x o (Wv ξ* Z₁ c₁)) , St ξ* Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk dupr2 (⇑ (cv* m)) (ψᵠ r t₁) , rwk (R-ψᵠ r r (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (P0ᵀ {q = r} rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* Z₁ C) (qwk dupr2 (⇑ (cv* m)) (ψᵠ r t₁))) (sym (run-wkC dupr2 (⇑ (cv* m)) D (ψᵠ r t₁))) (runᶜ-≅ o (rwk (R-ψᵠ r r (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (Psi r {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt n) (G→R (zG n)) (intoG (<→◃ r) (zG n))))
    zm : ∀ n → zt n ⊑ᵗ zt (suc n)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ m (≅ᴵ-refl k₁))) (P0ᵀ {q = r} (rf ξ* ξ* Z₁ Z₁ (∼ᶠ-refl ξ*) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl k₁))))))
    zm (suc n) = wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = r} (hm (zm n))))
```
