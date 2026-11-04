# 高度抽象: 尾部与下降

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFTail](LadderNFTail.lagda.md) 生成, 下面的说明是原文件的. `TL`: 值层的 `Good` 搬成 $m=0$, $c=0$ 的 `Gq`, 与 `OCF.Free.Tail` 同形. `ID`: 只要 `Gq g₂ n k 𝓧 x`, 就有 `Gq g′ (suc n) zero 𝓖 (ι↓ x)`; 新地板 $\text{flo}\,k$ 的 `Dem` 由 `Hq g₂` 给出, 这是 `Hq` 这一格唯一的用处. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfTail (𝕊 : HtS) where

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
open import OCF.Align.LadderInfClassF 𝕊
open import OCF.Align.LadderInfGood 𝕊
open import OCF.Align.LadderInfVis 𝕊
open import OCF.Align.LadderInfIota 𝕊
open import OCF.Align.LadderInfAdd 𝕊
open import OCF.Align.LadderInfTr 𝕊
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Force using (forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Eq using (s-invˢ; l-invˢ; i-respˢ; u-reflˢ; tf; ŝ≅; ĉ≅; upˡ; upʳ)
-- (同上)
open RestrQ
```

## §1 尾巴

```agda
Hl : ∀ {χ} k → ClT h₀ zero (flo k) χ → Cl k → Set
Hl zero      𝓖 𝓧 = 𝓧 idO
Hl (suc k)   𝓖 𝓧 = ∀ {C} → 𝓖 C → 𝓧 (tlo C)
Hl (lim f s) 𝓖 𝓧 = ∀ {C} → 𝓖 C → 𝓧 (tlo C)

demFlo : ∀ {k K X} (q : InF K (flo k)) → k ⊑ᴵ X → Dem X q
demFlo {k = suc k₀} ink (s⊑ e r) = inj₁ (via e r)
demFlo {k = lim f s} inb u = u

Dn₁ : ∀ {χ k₀ k} (r : k ◃₁ k₀) → Cl k₀ → ClT h₀ zero (flo k) χ
Dn₁ {χ} {k₀} r 𝓧 E = Ctxᶜ E × (Σ (Cx h₀ zero (flo k₀) χ) λ C → 𝓧 (tlo C) × (E ≈ᶜ C))

hdn₁ : ∀ {χ k₀ k} (r : k ◃₁ k₀) {𝓧 : Cl k₀} → Hl {χ} k (Dn₁ r 𝓧) (Dn r 𝓧)
hdn₁ {k = zero}    r = refl
hdn₁ {k = suc _}   r (x , C , c , o) = x , tlo C , c , tlo o
hdn₁ {k = lim _ _} r (x , C , c , o) = x , tlo C , c , tlo o

leUp : ∀ {k k₀} (r : k ◃₁ k₀) {L} → Ev L (flo k₀) → Ev L (flo k)
leUp {k} {k₀} r v = toFlo k (λ q → cvFlo k₀ v (τ₁ r q))

TL : ∀ {g χ k} {𝓖 : ClT h₀ zero (flo k) χ} {𝓧 : Cl k} {y : Ordˢ k} → Hl k 𝓖 𝓧 → (∀ {C} → 𝓖 C → 𝓥 C) → Good true 𝓧 y → y ≅ˢ y → Gq g h₀ zero 𝓖 (tl (flo k) (cvFlo k) y)
TL H H₂ bz ey = g0
TL {k = zero} H H₂ (b1 z≅) ey = gs 𝓥 H₂ g0 (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ c G → (λ { () }) , (λ i q₀ → ⊥-elim (no< q₀))) (λ c → Hq-zero _)
TL {k = zero} H H₂ (bs 𝓚 v eb g clk cgk ho) ey =
  gs 𝓥 H₂ (TL {𝓖 = 𝓥} {𝓧 = 𝓚} (v H) (λ c → c) g eb) (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ c G → (λ { () }) , (λ i q₀ → ⊥-elim (no< q₀))) (λ c → Hq-zero _)
TL {k = suc k₀} {𝓖 = 𝓖} H H₂ (bs {a = a} 𝓚 v eb g clk cgk ho) ey =
  gs (λ C → 𝓥 C × 𝓚 (tlo C)) (λ c₁ → H₂ c₁ , v (H c₁)) (TL {𝓖 = λ C → 𝓥 C × 𝓚 (tlo C)} {𝓧 = 𝓚} proj₂ proj₁ g eb)
     (λ (x , c₁) f _ → cxoᵀ f , clk tt c₁ (flo-over (cxoᵀ f) (λ t et G → flwᵀ f (tl (flo (suc k₀)) (cvFlo (suc k₀)) t) (R-tl et) G)))
     (λ x o (_ , c₁) → x , cgk tt x (tlo o) c₁)
     (λ (_ , c₁) G → (λ q → demFlo q (ho c₁ G)) , (λ i q₀ → ⊥-elim (no< q₀))) (λ c → Hq-zero _)
TL {k = lim f₀ s₀} {𝓖 = 𝓖} H H₂ (bs {a = a} 𝓚 v eb g clk cgk ho) ey =
  gs (λ C → 𝓥 C × 𝓚 (tlo C)) (λ c₁ → H₂ c₁ , v (H c₁)) (TL {𝓖 = λ C → 𝓥 C × 𝓚 (tlo C)} {𝓧 = 𝓚} proj₂ proj₁ g eb)
     (λ (x , c₁) f _ → cxoᵀ f , clk tt c₁ (flo-over (cxoᵀ f) (λ t et G → flwᵀ f (tl (flo (lim f₀ s₀)) (cvFlo (lim f₀ s₀)) t) (R-tl et) G)))
     (λ x o (_ , c₁) → x , cgk tt x (tlo o) c₁)
     (λ (_ , c₁) G → (λ q → demFlo q (ho c₁ G)) , (λ i q₀ → ⊥-elim (no< q₀))) (λ c → Hq-zero _)
TL H H₂ (bl h st) ey = gl (λ n → TL H H₂ (h n) (l-invˢ ey n)) (λ n → tl-congᵒ (st n))
TL {k = zero} H H₂ (bi {p = ()} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey
TL {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey =
  gi (λ C → 𝓥 C × 𝓖₀ (tlo C)) (λ c₁ → H₂ c₁ , inc₀ (H c₁)) (λ C → W (tlo C)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → TL {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)} (λ {C} c₁ → C , c₁ , refl) (λ c₁ → proj₁ (inc″ c₁))
        (hb (λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)) (λ { (C , c₁ , refl) → proj₂ (inc″ c₁) }) z ez
            (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , E , (C , c₁ , refl) , o) → x , C , c₁ , o })) g)))
        (i-respˢ ey ez))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) _ → cx′ , St c₀ (above cx′ (λ t et → wrap (tl (flo (suc k₀)) (cvFlo (suc k₀)) t) (R-tl et))))
     (λ x o (_ , c₀) → x , cg x (tlo o) c₀)
     (λ h → tl-congᵒ (hm h)) (λ d → R-tl (i-respˢ ey d))
TL {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey =
  gi (λ C → 𝓥 C × 𝓖₀ (tlo C)) (λ c₁ → H₂ c₁ , inc₀ (H c₁)) (λ C → W (tlo C)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → TL {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)} (λ {C} c₁ → C , c₁ , refl) (λ c₁ → proj₁ (inc″ c₁))
        (hb (λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)) (λ { (C , c₁ , refl) → proj₂ (inc″ c₁) }) z ez
            (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , E , (C , c₁ , refl) , o) → x , C , c₁ , o })) g)))
        (i-respˢ ey ez))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) _ → cx′ , St c₀ (above cx′ (λ t et → wrap (tl (flo (lim f₀ s₀)) (cvFlo (lim f₀ s₀)) t) (R-tl et))))
     (λ x o (_ , c₀) → x , cg x (tlo o) c₀)
     (λ h → tl-congᵒ (hm h)) (λ d → R-tl (i-respˢ ey d))
TL {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bu {r = zero} g) ey =
  gw (Dn₁ zero 𝓧) (λ {C} c₁ → Ctx-wkC C (H₂ c₁) , C , H c₁ , ≈ᶜ-wkˡ (leUp zero) sub-id (ctxᶜ-refl C (H₂ c₁)))
     (TL {𝓖 = Dn₁ zero 𝓧} {𝓧 = Dn zero 𝓧} (hdn₁ zero) proj₁ g (u-reflˢ zero ey))
TL {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bu {r = self n} g) ey =
  gw (Dn₁ (self n) 𝓧) (λ {C} c₁ → Ctx-wkC C (H₂ c₁) , C , H c₁ , ≈ᶜ-wkˡ (leUp (self n)) sub-id (ctxᶜ-refl C (H₂ c₁)))
     (TL {𝓖 = Dn₁ (self n) 𝓧} {𝓧 = Dn (self n) 𝓧} (hdn₁ (self n)) proj₁ g (u-reflˢ (self n) ey))
TL {k = zero} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀′ gg et eg m mm d₀ dE ch₀ chS) ey =
  gĉ C.ys C.hy C.dy C.G₀ (≅-refl⁰ _) C.Gk (λ k → ≅-refl⁰ _)
     (toZ-≅ et) (λ η e η′ e′ d → toZ-≅ (eg η e η′ e′ d)) (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d))
     (TL H H₂ g₀′ et)
     (λ n → TL {𝓖 = 𝓖} {𝓧 = 𝓧 ∧ 𝓑 (toLevel (C.ys n) (C.hy n))} (H , bp (C.P n)) H₂ (gg _ (C.dy n) (H , bp (C.P n))) (eg _ _ _ _ (≅ᴵ-refl _)))
     (tl-congᵒ (m _ _)) (λ n → tl-congᵒ (mm _ _ _ _ (C.lmono n)))
  where module C = Ch0 𝓑 H g₀′ gg m mm d₀ dE ch₀ chS
TL {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀′ gg et eg m mm d₀ dE ch₀ chS) ey =
  gŝ (λ η C → 𝓑 η (tlo C)) Bc (TL {𝓖 = 𝓖} {𝓧 = 𝓧} (λ {C} c₁ → H c₁) H₂ g₀′ et)
     (λ η e → TL {𝓖 = λ C → 𝓖 C × 𝓑 η (tlo C)} {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c₁ , b) → H c₁ , b) (λ c₁ → H₂ (proj₁ c₁)) (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
     (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d)) (λ η e → tl-congᵒ (m η e)) (λ η e η′ e′ u → tl-congᵒ (mm η e η′ e′ u))
     (λ c₁ G → d₀ (H c₁) G) (λ η e c₁ b G → dE η e (H c₁) b G) (λ c₁ G → ch₀ (H c₁) G) (λ η e c₁ b G → chS η e (H c₁) b G)
TL {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀′ gg et eg m mm d₀ dE ch₀ chS) ey =
  gŝ (λ η C → 𝓑 η (tlo C)) Bc (TL {𝓖 = 𝓖} {𝓧 = 𝓧} (λ {C} c₁ → H c₁) H₂ g₀′ et)
     (λ η e → TL {𝓖 = λ C → 𝓖 C × 𝓑 η (tlo C)} {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c₁ , b) → H c₁ , b) (λ c₁ → H₂ (proj₁ c₁)) (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
     (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d)) (λ η e → tl-congᵒ (m η e)) (λ η e η′ e′ u → tl-congᵒ (mm η e η′ e′ u))
     (λ c₁ G → d₀ (H c₁) G) (λ η e c₁ b G → dE η e (H c₁) b G) (λ c₁ G → ch₀ (H c₁) G) (λ η e c₁ b G → chS η e (H c₁) b G)
TL H H₂ (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) (ĉ≅ ec dt dg eo eO) =
  gĉ ys hy dy G₀ l₀ Gg lE dt dg (R-tl eo) (λ η e η′ e′ d → R-tl (eO η e η′ e′ d))
     (TL H H₂ go eo) (λ k → TL H H₂ (gO k) (eO _ _ _ _ (≅ᴵ-refl _))) (tl-congᵒ mo) (λ k → tl-congᵒ (mO k))
```

## §2 下降

```agda

dmD : ∀ {n m k X φ} {χ : Fv} → Dm n X φ χ → k ⊑ᴵ X → Dm m X φ (cap χ n (flo k))
dmD {n} {m} {k} {X} {φ} {χ} (d₁ , d₂) u = d₁ , go
  where
  cst : ∀ {f f′ : Flr} → f′ ≡ f → (∀ {K} (r : InF K f) → Dem X r) → ∀ {K} (r : InF K f′) → Dem X r
  cst refl h r = h r
  go : ∀ i → i <ᴸ m → ∀ {K} (r : InF K (cap χ n (flo k) i)) → Dem X r
  go i _ = case-tri i n
    (λ l → cst (cap-lt χ (flo k) l) (d₂ i l))
    (λ { refl → cst (cap-self χ n (flo k)) (λ r → demFlo r u) })
    (λ l → cst (cap-gt χ (flo k) l) (λ ()))

pD-refl : ∀ {n k φ χ ψ ρ} {E : Cx n k φ χ} {D : Cx n k ψ ρ} → Ctxᶜ E → E ≈ᶜ D → E ≈ᶜ D
pD-refl x o = o

module IDM {n m : Ht} (qd : n <ᴸ m) where
  gΩD : ∀ {g′ k φ χ} {𝓖 : ClT m zero φ (cap χ n (flo k))} {𝓧 : ClT n k φ χ} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {k₁} {r : k₁ <ᴵ k} {h : ∀ ξ ζ → Us n k₁ (<→◃ r) ξ ζ → Q n k (ξ ⊔ φ) (lo n ζ ∪ χ)} →
        (∀ {C} → 𝓖 C → 𝓧 (pD {q = qd} C)) → (∀ {C} → 𝓖 C → 𝓥 C) →
        (𝓖₀ : ∀ ξ ζ → ClT n k (ξ ⊔ φ) (lo n ζ ∪ χ)) →
        (∀ ξ ζ {C} {C′ : Cx n k (ξ ⊔ φ) (lo n ζ ∪ χ)} → 𝓧 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ ζ C′) →
        (W : ∀ ξ ζ → Cx n k (ξ ⊔ φ) (lo n ζ ∪ χ) → Cx n k₁ ξ ζ) →
        (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → ∀ (u : Q n k₁ ξ ζ) → Rq n k₁ k₁ u u → runᶜ (W ξ ζ C) u ≅ˢ runᶜ C (h ξ ζ (intoU (<→◃ r) u))) →
        (∀ (𝓔 : ∀ ξ ζ → ClT n k (ξ ⊔ φ) (lo n ζ ∪ χ)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → 𝓖₀ ξ ζ C) → ∀ ξ ζ (z : Q n k₁ ξ ζ) → Rq n k₁ k₁ z z → LG n k g₂ (<→◃ r) (W ξ ζ ⟪ 𝓔 ξ ζ ⟫ᵀ) z → Gq g₂ n k (𝓔 ξ ζ) (h ξ ζ (intoU (<→◃ r) z))) →
        (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → VisQT k₁ (W ξ ζ C)) →
        (∀ ξ ζ {C} {C′ : Cx n k (ξ ⊔ φ) (lo n ζ ∪ χ)} → 𝓖₀ ξ ζ C → AboveΩ C′ (W ξ ζ C) → ⊤ → 𝓖₀ ξ ζ C′) →
        (∀ ξ ξ′ ζ ζ′ {C : Cx n k (ξ ⊔ φ) (lo n ζ ∪ χ)} {C′ : Cx n k (ξ′ ⊔ φ) (lo n ζ′ ∪ χ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ ζ′ C′ → 𝓖₀ ξ ζ C) →
        (∀ {ξ ξ′ ζ ζ′} {z : Q n k₁ ξ ζ} {z′ : Q n k₁ ξ′ ζ′} → z ⊑ᵗ z′ → h ξ ζ (intoU (<→◃ r) z) ⊑ᵗ h ξ′ ζ′ (intoU (<→◃ r) z′)) →
        (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k₁ ξ ζ) (z′ : Q n k₁ ξ′ ζ′) → Rq n k₁ k₁ z z′ → Rq n k k (h ξ ζ (intoU (<→◃ r) z)) (h ξ′ ζ′ (intoU (<→◃ r) z′))) →
        Gq g′ m zero 𝓖 (ι↓ qd (qΩ fe r h))

  ID : ∀ {g′ k φ χ} {𝓖 : ClT m zero φ (cap χ n (flo k))} {𝓧 : ClT n k φ χ} {x : Q n k φ χ} → (∀ {C} → 𝓖 C → 𝓧 (pD {q = qd} C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gq g₂ n k 𝓧 x → Gq g′ m zero 𝓖 (ι↓ qd x)
  ID H H₂ g0 = g0
  ID H H₂ (gs 𝓚 v k clk cgk ho hq) =
    gs (λ D → 𝓥 D × 𝓚 (pD {q = qd} D)) (λ c → H₂ c , v (H c)) (ID proj₂ proj₁ k)
       (λ {O₁} {C″} (x , c₁) f _ → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (ι↓ qd t) (R-ι↓ qd (≅ᴵ-refl _) rt) G)) tt)
       (λ x o (_ , c₁) → x , cgk x (pD {q = qd} o) c₁)
       (λ (_ , c₁) G → dmD (ho c₁ G) (hq c₁ G))
       (λ _ → Hq-zero _)
  ID H H₂ (gl f st) = gl (λ n → ID H H₂ (f n)) (λ n → ιD-congᵗ (st n))
  ID {g′} {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
    gi (λ D → 𝓥 D × 𝓖₀ (pD {q = qd} D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (pD {q = qd} D)) (λ (x , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez gz → ID {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pD {q = qd} D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
          (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pD {q = qd} D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) gz)))
       (λ (x , c₀) → Wv c₀)
       (λ (x , c₀) (aboveV cx′ wrap) _ → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (ι↓ qd t) (R-ι↓ qd (≅ᴵ-refl _) rt))) tt)
       (λ x o (_ , c₀) → x , cg x (pD {q = qd} o) c₀)
       (λ h → ιD-congᵗ (hm h)) (λ d → R-ι↓ qd (≅ᴵ-refl _) (rf d))
  ID {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pD {q = qd} D)) Bc (ID H H₂ g₀′)
       (λ η e → ID {𝓖 = λ D → 𝓖 D × 𝓑 η (pD {q = qd} D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
       (R-ι↓ qd (≅ᴵ-refl _) et) (λ η e η′ e′ d → R-ι↓ qd (≅ᴵ-refl _) (eg η e η′ e′ d)) (λ η e → ιD-congᵗ (m₁ η e)) (λ η e η′ e′ u → ιD-congᵗ (mm η e η′ e′ u))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  ID H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-ι↓ qd (≅ᴵ-refl _) r₁) (λ η e η′ e′ d → R-ι↓ qd (≅ᴵ-refl _) (r₂ η e η′ e′ d)) (ID H H₂ go) (λ k → ID H H₂ (gO k)) (ιD-congᵗ mo) (λ k → ιD-congᵗ (mO k))
  ID H H₂ (gw 𝓖₁ inc₁ gk) =
    gw (λ E → 𝓥 E × 𝓖₁ (pD {q = qd} E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (ID proj₂ proj₁ gk)
  ID {φ = φ₀ ⊔ fk zero} H H₂ (gclo {φ = φ₀} 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gclo (λ D → 𝓥 D × 𝓖ᵗ (pD {q = qd} D)) (λ c → H₂ c , inc₁ (H c)) (λ x o (_ , c₁) → x , cgᵗ x (pD {q = qd} o) c₁)
       (λ η D → 𝓥 D × 𝓖ᵍ η (pD {q = qd} D))
       (λ e x o (_ , c₁) → x , Bc e x (pD {q = qd} o) c₁)
       (ID proj₂ proj₁ gt) (λ η → ID proj₂ proj₁ (gg η))
       (R-ι↓ qd (≅ᴵ-refl _) rt) (λ η η′ e → R-ι↓ qd (≅ᴵ-refl _) (rg η η′ e))
       (λ η h → ιD-congᵗ (m₁ η h)) (λ η η′ h u → ιD-congᵗ (mm η η′ h u))
       (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
       (λ (_ , c₁) G x o → x , ch₀ c₁ G x (pD {q = qd} o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (pD {q = qd} o))
  ID {k = kᵈ} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gcl {n = j} {q = q} {ψ = ψ} {s = s} {t = t₀} {h = g₁′} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gcl (λ D → 𝓥 D × 𝓖ᵗ (pD {q = qd} D)) (λ c → H₂ c , inc₁ (H c)) (λ η D → 𝓥 D × 𝓖ᵍ η (pD {q = qd} (wkC (λ e → e) (LL η) D)))
       (λ {η} {η′} {C} {C′} e x o (_ , c₁) → x , Bc e (Ctx-wkC C′ x) (pD {q = qd} (wk≈ (λ u → u) (LL η′) (λ u → u) (LL η) o)) c₁)
       (ID proj₂ proj₁ gt)
       (λ η → gw (λ E → 𝓥 E × 𝓖ᵍ η (pD {q = qd} E)) (λ {D} (x , c₁) → Ctx-wkC D x , c₁) (ID proj₂ proj₁ (gg η)))
       (R-ι↓ qd (≅ᴵ-refl _) rt) (λ η η′ d → rwk (R-ι↓ qd (≅ᴵ-refl _) (rg η η′ d)))
       (λ η h → wk-rᵗ (ιD-congᵗ (m₁ η h))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (ιD-congᵗ (mm η η′ h u))))
       (λ (_ , c₁) G r₁ → dt c₁ G r₁)
       (λ η {D} (_ , c₁) → at≡ (run-wkC (λ u → u) (LL η) D (ι↓ qd (g₁′ η))) {P = λ X → ∀ {K} (r₁ : InF K ψ) → Dem X r₁} (λ G₁ r₁ → dg η c₁ G₁ r₁))
       (λ {D} (x₀ , c₁) G {C′} x o → x , ch₀ c₁ G (Ctx-wkC C′ x) (pD {q = qd} (≈ᶜ-wkˡ (λ u → u) (LL (lvG G)) o)))
       (λ η {D} (x₀ , c₁) → at≡ (run-wkC (λ u → u) (LL η) D (ι↓ qd (g₁′ η))) {P = λ X → ∀ {C′ : Cx m zero φ (upd (cap χ n (flo kᵈ)) j (ψ ⊔ fk X))} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓥 C′ × 𝓖ᵍ X (pD {q = qd} (wkC (λ e → e) (LL X) C′))}
           (λ G₁ {C′} x o → x , chS η c₁ G₁ (Ctx-wkC C′ x) (pD {q = qd} (wk≈ (λ u → u) (LL (lvG G₁)) (λ u → u) (LL η) o))))
    where
    LL : ∀ η → Sub m (upd (cap χ n (flo kᵈ)) j (ψ ⊔ fk η)) (cap (upd χ j (ψ ⊔ fk η)) n (flo kᵈ))
    LL η = ⇑ (c-sw {χ} _ q)
  ID {k = kᵈ} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ↓ {n = j} {k = k₁} {q = q₁} {fe = fe} {ac = ac} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
    gΩ↓ (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D)))
       (λ ξ ζ {C} {C′} c₁ x o → x , inc₀ ξ ζ (H c₁) (Ctx-wkC C′ x) (pD {q = qd} (≈ᶜ-wkˡ (λ u → u) (LL ζ) o)))
       (λ ξ ζ D → W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D)))
       (λ ξ ζ {D} (x , c₀) u ru → subst (λ w → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ runᶜ D (H̃ ξ ζ w)) (sym (out-intoV Q′ u)) (subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru)))
       (λ 𝓔′ inc″ ξ ζ z rz₁ gz → subst (λ w → Gq _ m zero (𝓔′ ξ ζ) (H̃ ξ ζ w)) (sym (out-intoV Q′ z)) (
          gw (λ E → 𝓥 E × 𝓧₃ 𝓔′ ξ ζ E) (λ {D} c₁ → Ctx-wkC D (proj₁ (inc″ ξ ζ c₁)) , D , c₁ , refl)
            (ID (λ { (_ , D , c₁ , refl) → D , c₁ , refl }) proj₁
              (hb (𝓧₄ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ z rz₁
                 (intoGV q₁ (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV Q′ gz)))))))
       (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) _ → cx′ , St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t rt →
            let Wp = wrap (qwk (λ e → e) (LL ζ) (ι↓ qd t)) (rwk (R-ι↓ qd (≅ᴵ-refl _) rt))
            in proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
               subst (λ v → v ≅ˢ runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) (proj₁ Wp)) (sym (run-wkC (λ e → e) (LL ζ) C′ (ι↓ qd t))) (proj₂ (proj₂ (proj₂ Wp))))) tt)
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (x′ , c₀) → x , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pD {q = qd} (wk≈ (λ u → u) (LL ζ) (λ u → u) (LL ζ′) o)) c₀)
       (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ w w′ → H̃ ξ ζ w ⊑ᵗ H̃ ξ′ ζ′ w′) (sym (out-intoV Q′ z)) (sym (out-intoV Q′ z′)) (wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u)))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (H̃ ξ ζ w) (H̃ ξ′ ζ′ w′)) (sym (out-intoV Q′ z)) (sym (out-intoV Q′ z′)) (rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    where
    Q′ = tr< q₁ qd
    LL : ∀ ζ → Sub m (lo j ζ ∪ cap χ n (flo kᵈ)) (cap (lo j ζ ∪ χ) n (flo kᵈ))
    LL ζ = ⇑ (c-∪ {lo j ζ} {χ} _)
    H̃ : ∀ ξ ζ → Q j k₁ ξ ζ → Q m zero (ξ ⊔ φ) (lo j ζ ∪ cap χ n (flo kᵈ))
    H̃ ξ ζ w = qwk (λ e → e) (LL ζ) (ι↓ qd (h ξ ζ (intoV q₁ w)))
    𝓧₃ : (∀ ξ ζ → ClT m zero (ξ ⊔ φ) (lo j ζ ∪ cap χ n (flo kᵈ))) → ∀ ξ ζ → ClT m zero (ξ ⊔ φ) (cap (lo j ζ ∪ χ) n (flo kᵈ))
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ wkC (λ e → e) (LL ζ) D)
    𝓧₄ : (∀ ξ ζ → ClT m zero (ξ ⊔ φ) (lo j ζ ∪ cap χ n (flo kᵈ))) → ∀ ξ ζ → ClT n kᵈ (ξ ⊔ φ) (lo j ζ ∪ χ)
    𝓧₄ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pD {q = qd} (wkC (λ e → e) (LL ζ) D))
  ID {k = suc a} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ {k = k₁} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) = gΩD H H₂ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf
  ID {k = lim f s} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ {k = k₁} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) = gΩD H H₂ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf
  ID {k = suc a} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gm {r = zero} {z = z} zc rz₁ gx) =
    gw 𝓖₁ (λ {C} c → Ctx-wkC C (H₂ c) , C , c , ctxᶜ-refl (wkC (λ e → e) LLm C) (Ctx-wkC C (H₂ c)))
       (ID {𝓖 = 𝓖₁} {𝓧 = Dq zero 𝓧} (λ { (x , C , c , o) → x , pD {q = qd} C , H c , tt , pD {q = qd} o }) proj₁ (zc 𝓧 (λ c → c)))
    where
    LLm : Sub m (cap χ n (flo (suc a))) (cap χ n (flo a))
    LLm = ⇑ (cap-map n (tighten zero))
    𝓖₁ : ClT m zero φ (cap χ n (flo a))
    𝓖₁ E = 𝓥 E × (Σ _ λ C → 𝓖 C × (E ≈ᶜ wkC (λ e → e) LLm C))
  ID {k = lim f s} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gm {r = self i} {z = z} zc rz₁ gx) =
    gw 𝓖₁ (λ {C} c → Ctx-wkC C (H₂ c) , C , c , ctxᶜ-refl (wkC (λ e → e) LLm C) (Ctx-wkC C (H₂ c)))
       (ID {𝓖 = 𝓖₁} {𝓧 = Dq (self i) 𝓧} (λ { (x , C , c , o) → x , pD {q = qd} C , H c , tt , pD {q = qd} o }) proj₁ (zc 𝓧 (λ c → c)))
    where
    LLm : Sub m (cap χ n (flo (lim f s))) (cap χ n (flo (f i)))
    LLm = ⇑ (cap-map n (tighten (self i)))
    𝓖₁ : ClT m zero φ (cap χ n (flo (f i)))
    𝓖₁ E = 𝓥 E × (Σ _ λ C → 𝓖 C × (E ≈ᶜ wkC (λ e → e) LLm C))

  gΩD {k = kᵈ} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {k₁ = k₁} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf =
    gΩ↓ {q = qd} (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D)))
       (λ ξ ζ {C} {C′} c₁ x o → x , inc₀ ξ ζ (H c₁) (Ctx-wkC C′ x) (pD {q = qd} (≈ᶜ-wkˡ (λ u → u) (LL ζ) o)))
       (λ ξ ζ D → W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D)))
       (λ ξ ζ {D} (x , c₀) u ru → subst (λ w → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ runᶜ D (H̃ ξ ζ w)) (sym (out-intoV qd u)) (subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoU (<→◃ r) u)))) (Wf ξ ζ c₀ u ru)))
       (λ 𝓔′ inc″ ξ ζ z rz₁ gz → subst (λ w → Gq _ m zero (𝓔′ ξ ζ) (H̃ ξ ζ w)) (sym (out-intoV qd z)) (
          gw (λ E → 𝓥 E × 𝓧₃ 𝓔′ ξ ζ E) (λ {D} c₁ → Ctx-wkC D (proj₁ (inc″ ξ ζ c₁)) , D , c₁ , refl)
            (ID (λ { (_ , D , c₁ , refl) → D , c₁ , refl }) proj₁
              (hb (𝓧₄ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ z rz₁
                 (intoG (<→◃ r) (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV qd gz)))))))
       (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) _ → cx′ , St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t rt →
            let Wp = wrap (qwk (λ e → e) (LL ζ) (ι↓ qd t)) (rwk (R-ι↓ qd (≅ᴵ-refl _) rt))
            in proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
               subst (λ v → v ≅ˢ runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) (proj₁ Wp)) (sym (run-wkC (λ e → e) (LL ζ) C′ (ι↓ qd t))) (proj₂ (proj₂ (proj₂ Wp))))) tt)
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (x′ , c₀) → x , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pD {q = qd} (wk≈ (λ u → u) (LL ζ) (λ u → u) (LL ζ′) o)) c₀)
       (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ w w′ → H̃ ξ ζ w ⊑ᵗ H̃ ξ′ ζ′ w′) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u)))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (H̃ ξ ζ w) (H̃ ξ′ ζ′ w′)) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    where
    LL : ∀ ζ → Sub m (lo n ζ ∪ cap χ n (flo kᵈ)) (cap (lo n ζ ∪ χ) n (flo kᵈ))
    LL ζ = ⇑ (c-∪ {lo n ζ} {χ} _)
    H̃ : ∀ ξ ζ → Q n k₁ ξ ζ → Q m zero (ξ ⊔ φ) (lo n ζ ∪ cap χ n (flo kᵈ))
    H̃ ξ ζ w = qwk (λ e → e) (LL ζ) (ι↓ qd (h ξ ζ (intoU (<→◃ r) w)))
    𝓧₃ : (∀ ξ ζ → ClT m zero (ξ ⊔ φ) (lo n ζ ∪ cap χ n (flo kᵈ))) → ∀ ξ ζ → ClT m zero (ξ ⊔ φ) (cap (lo n ζ ∪ χ) n (flo kᵈ))
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ wkC (λ e → e) (LL ζ) D)
    𝓧₄ : (∀ ξ ζ → ClT m zero (ξ ⊔ φ) (lo n ζ ∪ cap χ n (flo kᵈ))) → ∀ ξ ζ → ClT n kᵈ (ξ ⊔ φ) (lo n ζ ∪ χ)
    𝓧₄ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pD {q = qd} (wkC (λ e → e) (LL ζ) D))
```
