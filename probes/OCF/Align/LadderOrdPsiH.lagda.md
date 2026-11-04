# 序数高度: 目标在高度 $H$ 的闭包定理

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfPsiH](LadderInfPsiH.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 对高度结构 `HtB` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFPsiH](LadderNFPsiH.lagda.md) 生成, 下面的说明是原文件的. `PsiHM.PsiH qH ok e p : Gq g m c 𝓧 x → Gq g₂ H t 𝓖 (Ψ qH ok e p x)`, 对一切 $H<m$, $t<w_H$, 只要 $C\in\mathcal G$ 推出 `pΨ …` ∈ $\mathcal X$ 且 $C$ 在 `VisQT t`. 这是值层 `T̄` 上移一层: 高度 $n\ge H$ 的闭包落成 `gŝ`, 界由 `rdT` (目标) 与 `dt`, `dg` (地板) 给 (`bd⊑`); 高度 $n\ge H$ 的节点走链或穿透. **没有对 $m$, $t$ 的归纳.** 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdPsiH (𝕊 : HtB) where

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
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdRules3 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import OCF.Align.LadderOrdStrict2 𝕊
open import OCF.Align.LadderOrdClass 𝕊
open import OCF.Align.LadderOrdClassF 𝕊 using (inp-map)
open import OCF.Align.LadderOrdGood 𝕊
open import OCF.Align.LadderOrdVis 𝕊
open import OCF.Align.LadderOrdIota 𝕊
open import OCF.Align.LadderOrdAdd 𝕊
open import OCF.Align.LadderOrdTr 𝕊
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.LadderOrdPsi 𝕊
open import OCF.Align.LadderOrdRead 𝕊
open import OCF.Free.Floor using (bound; Top; Bd; Fc; ubd; evF; iF; FM; FB; liftEv; bound-≅)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Eq using (⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ)
open RestrQ

Kl-wk₂ : ∀ {m k φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {D : Cx m k ψ ρ} → VisQT k D → VisQT k (wkC le lc D)
Kl-wk₂ {le = le} {lc = lc} {D = D} v = VisQT-≈ (Ctx-wkC D (cxQ (vQ v))) (≈ᶜ-wkˡ le lc (ctxᶜ-refl D (cxQ (vQ v)))) v

one⊑B : ∀ {i ℓ φ} (B : Top i ℓ (φ ⊔ fk zero)) {η} → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
one⊑B B e = ⊑ᴵ-trans (s⊑ z≅ᴵ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)
  where z≅ᴵ = ≅ᴵ-refl zero

bd⊑ : ∀ {i ℓ ψ X} (B : Top i ℓ (ψ ⊔ fk zero)) → suc i ⊑ᴵ X → (∀ {K} (k : InF K ψ) → Dem X k) → Bd B ⊑ᴵ X
bd⊑ B (s⊑ e q) dm = ubd B (via e q) (λ { (inl k) → dm k ; (inr ink) → inj₂ z≅ })

module PsiHM (Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)) where
  open PsiM Ω̇G

  PsiH : ∀ {g H m c t φ χ w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) {𝓖 : ClT H t (Fl ⊔ φ) (Z* χ)} {𝓧 : ClT m c φ χ} {x : Q m c φ χ} → (∀ {C} → 𝓖 C → 𝓧 (pΨ qH ok e p C)) → (∀ {C} → 𝓖 C → VisQT t C) → Gq g m c 𝓧 x → Gq g₂ H t 𝓖 (Ψ qH ok e p x)
  PsiH {H = H} {t = t} qH ok e p H₁ H₂ g0 = gw (KQ g₂ t) (λ {C} c → vQ (Kl-wk₂ {le = proj₁} {lc = fc*} (H₂ c))) (Ω̇G g₂ H t)
  PsiH {H = H} {m} {c = c} {t = t} {φ = φ} {χ = χ} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gs {a = a} 𝓚 v k clk cgk ho hq) =
    gl (λ n → Gmono (λ c₁ → H₂ c₁ , v (H₁ c₁)) (rep-good n)) mono
    where
    𝓐 : ClT H t (Fl ⊔ φ) (Z* χ)
    𝓐 C = VisQT t C × 𝓚 (pΨ qH ok e p C)
    X = Ψ qH ok e p a
    gX : Gq g₂ H t 𝓐 X
    gX = PsiH qH ok e p proj₂ proj₁ k
    ra = G→R k
    rX : Rq H t t X X
    rX = R-Ψ qH ok e p ok e p (≅ᴵ-refl _) ra
    Xfl : ∀ n → X ⊑ᵀ repᵠ X (suc n)
    Xfl zero = R→⊑ᵀ rX
    Xfl (suc n) = wk-rᵀ (B1ᵀ rX (Xfl n))
    rR : ∀ n → Rq H t t (repᵠ X n) (repᵠ X n)
    rR n = R-repᵠ (∼ᶠ-refl _) (Sim∼-refl _) rX n
    ΩX : Ω̇ H t ⊑ᵀ X
    ΩX = H0ᵀ ra (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t)))
    ΩR : ∀ n → Ω̇ H t ⊑ᵀ repᵠ X (suc n)
    ΩR n = ⊑ᵀ-trans ΩX (Xfl n)
    wf : ∀ n → WFl (repᵠ X (suc n))
    wf n = wfl (rR (suc n)) (⊑ᵀ-trans (H0ᵀ ra (𝟏⊑Ω̇ H t)) (Xfl n))
    clA : ∀ n {O₁ C″} → 𝓐 O₁ → FlOverᵀ (repᵠ X (suc n)) O₁ C″ → 𝓐 C″
    clA n {O₁} {C″} (x , c₁) f = Kl-fl g₂ proj₁ fc* (ΩR n) x f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t₁ rt G →
      let L = flwᵀ f (Ψ qH ok e p t₁) (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) G
          N = Xfl n (ctxᶜ-refl O₁ (cxQ (vQ x))) (proj₁ L)
      in proj₁ N , ⊑-trans (proj₂ N) (proj₂ L))) (ndg _ tt)
    Dm↓ : ∀ {X₁} → Dm m X₁ φ χ → Dm H X₁ (Fl ⊔ φ) (Z* χ)
    Dm↓ d = (λ q → demFl q (proj₁ d)) , (λ i r q → demFl q (proj₂ d i (tr< r qH)))
    hoA : ∀ n {C} → 𝓐 C → HonT (repᵠ X (suc n)) C
    hoA n {C} (x , c₁) G =
      let N = Xfl n (ctxᶜ-refl C (cxQ (vQ x))) G
          U = toLevel-⊑ (forceᴺ-HS _ (proj₁ N)) (forceᴺ-HS _ G) (proj₂ N)
      in Dm↓ ((λ k₁ → demUp k₁ U (proj₁ (ho c₁ (proj₁ N)) k₁)) , (λ i r k₁ → demUp k₁ U (proj₂ (ho c₁ (proj₁ N)) i r k₁)))
    press : ∀ n {C} → 𝓐 C → 𝓐 (pa (repᵠ X (suc n)) (wkC (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) C))
    press n {C} (x , c₁) = KlUp g₂ {D = C} (wf n , Ctx-wkC C (cxQ (vQ x))) proj₁ fc* proj₁ fc*
        (λ y ry → qwk (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) (repᵠ X (suc n) ⊞ y) , wk-rᵀ (B1ᵀ ry (ΩR n)) , subst (λ w₁ → runᶜ (wkC (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) C) (repᵠ X (suc n) ⊞ y) ≅ˢ w₁) (run-wkC (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) C (repᵠ X (suc n) ⊞ y)) (runᶜ-≅ (≈ᶜ-reflʳ (≈ᶜ-wkʳ (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) (ctxᶜ-refl C (cxQ (vQ x))))) (R-⊞ (∼ᶠ-refl _) (Sim∼-refl _) (rR (suc n)) ry))) x ,
      clk c₁ (flo-overᵀ (wf n , Ctx-wkC C (cxQ (vQ x))) (λ t₁ rt G →
      B1ᵀ {x = X} {W = repᵠ X (suc n)} (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) (Xfl n) (≈ᶜ-wkʳ (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) (ctxᶜ-refl C (cxQ (vQ x)))) G)) (ndg _ tt)
    dup-𝓐 : ∀ {C : Cx H t (Fl ⊔ φ) (Z* χ)} → 𝓐 C → 𝓐 (wkC proj₁ pr₁ᶜ (wkC (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) C))
    dup-𝓐 {C} (x , c₁) =
      let cc = cxQ (vQ x)
          oo = ≈ᶜ-wkˡ proj₁ pr₁ᶜ (≈ᶜ-wkˡ (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) (ctxᶜ-refl C cc))
          c₂ = Ctx-wkC (wkC (λ e₁ → e₁ , e₁) (λ i r e₁ → e₁ , e₁) C) (Ctx-wkC C cc)
      in VisQT-≈ c₂ oo x , cgk c₂ (pΨ oo) c₁
    rep-good : ∀ n → Gq g₂ H t 𝓐 (repᵠ X n)
    rep-good zero = g0
    rep-good (suc zero) = gX
    rep-good (suc (suc n)) =
      gw (λ E → 𝓐 (wkC proj₁ pr₁ᶜ E) × 𝓐 (pa (repᵠ X (suc n)) E))
         (λ {C} c₁ → dup-𝓐 c₁ , press n c₁)
         (AddT.Add {W = repᵠ X (suc n)} (rep-good (suc n)) (wf n)
                   (λ x o (y , c₁) → VisQT-≈ x o y , cgk x (pΨ o) c₁) (clA n) (λ c₁ → cxQ (vQ (proj₁ c₁))) (hoA n) (λ c₁ → hoK g₂ (proj₁ c₁) proj₁ fc* (ΩR n))
                   {g′ = g₂} refl {𝓐₁ = λ E → 𝓐 (wkC proj₁ pr₁ᶜ E) × 𝓐 (pa (repᵠ X (suc n)) E)} {𝓧 = 𝓐} proj₁ proj₂ gX)
    mono : ∀ n → repᵠ X n ⊑ᵗ repᵠ X (suc n)
    mono zero = ⊑ᵀ→ᵗ rz (zero-lᵀ rX)
    mono (suc n) = wk-rᵗ (⊑ᵀ→ᵗ (rR (suc n)) (B1ᵀ rX (R→⊑ᵀ (rR (suc n)))))
  PsiH qH ok e p H₁ H₂ (gl f st) = gl (λ n → PsiH qH ok e p H₁ H₂ (f n)) (λ n → Ψ-congᵗ (st n))
  PsiH {H = H} {t = t} {φ = φ} {χ = χ} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gi {j = j} {f = f} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gi (λ D → VisQT t D × 𝓖₀ (pΨ qH ok e p D)) (λ c → H₂ c , inc₀ (H₁ c)) (λ D → W₀ (pΨ qH ok e p D)) (λ (x , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez gz → PsiH qH ok e p {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pΨ qH ok e p D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
          (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pΨ qH ok e p D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) gz)))
       (λ (x , c₀) → Wv c₀)
       (λ {D} {C′} (x , c₀) (aboveV cx′ wrap) nd →
          KlUp g₂ {D = D} cx′ proj₁ fc* proj₁ fc* (λ y ry →
            let Wp = wrap y ry
                u = proj₁ Wp
                eu = proj₁ (proj₂ Wp)
            in Ψ qH ok e p (f u) , H0ᵀ (rf eu) (R→⊑ᵀ (RΩ̇ _ (≅ᴵ-refl _))) , ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf c₀ u eu)) x ,
          St c₀ (aboveV cx′ (λ t₁ rt → wrap (Ψ qH ok e p t₁) (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt))) (ndg _ tt))
       (λ x o (y , c₀) → VisQT-≈ x o y , cg x (pΨ o) c₀)
       (λ h → Ψ-congᵗ (hm h)) (λ d → R-Ψ qH ok e p ok e p (≅ᴵ-refl _) (rf d))
  PsiH qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pΨ qH ok e p D)) Bc (PsiH qH ok e p H₁ H₂ g₀′)
       (λ η e₁ → PsiH qH ok e p {𝓖 = λ D → 𝓖 D × 𝓑 η (pΨ qH ok e p D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H₁ c , b) (λ (c , b) → H₂ c) (gg η e₁))
       (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) et) (λ η e₁ η′ e′ d → R-Ψ qH ok e p ok e p (≅ᴵ-refl _) (eg η e₁ η′ e′ d)) (λ η e₁ → Ψ-congᵗ (m₁ η e₁)) (λ η e₁ η′ e′ u → Ψ-congᵗ (mm η e₁ η′ e′ u))
       (λ c G → d₀ (H₁ c) G) (λ η e₁ c b G → dE η e₁ (H₁ c) b G) (λ c G → ch₀ (H₁ c) G) (λ η e₁ c b G → chS η e₁ (H₁ c) b G)
  PsiH qH ok e p H₁ H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) r₁) (λ η e₁ η′ e′ d → R-Ψ qH ok e p ok e p (≅ᴵ-refl _) (r₂ η e₁ η′ e′ d)) (PsiH qH ok e p H₁ H₂ go) (λ k → PsiH qH ok e p H₁ H₂ (gO k)) (Ψ-congᵗ mo) (λ k → Ψ-congᵗ (mO k))
  PsiH {t = t} qH ok e p H₁ H₂ (gw {le = le} {lc = lc} 𝓖₁ inc₁ k) =
    gw (λ E → VisQT t E × 𝓖₁ (pΨ qH ok (λ i h r → lc i r (e i h r)) p E)) (λ {C} c → Kl-wk₂ (H₂ c) , inc₁ (H₁ c)) (PsiH qH ok (λ i h r → lc i r (e i h r)) p proj₂ proj₁ k)
  PsiH qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gm zc rz₁ gx) = PsiH qH ok e p {𝓖 = 𝓖} {𝓧 = λ C → 𝓧 C × Nd C} (λ c → H₁ c , tt) H₂ gx
  PsiH {H = H} {m} {t = t} {φ = φ₀ ⊔ fk zero} {χ = χ} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gclo {φ = φ₀} {t = t₀} {h = g₁′} 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gw (𝓖ₐ 𝓖ᵗ) (λ {C} c₁ →
           let cc = cxQ (vQ (H₂ c₁))
               o₁ = ≈ᶜ-wkˡ asr sub-id (≈ᶜ-wkˡ asl sub-id (ctxᶜ-refl C cc))
           in Kl-wk₂ (H₂ c₁) , cgᵗ (Ctx-wkC (wkC asl sub-id C) (Ctx-wkC C cc)) (pΨ o₁) (inc₁ (H₁ c₁)))
       (gclo (𝓖ₐ 𝓖ᵗ) (λ c₁ → c₁)
         (λ {C} {C′} x o (y , c₁) → VisQT-≈ x o y , cgᵗ (Ctx-wkC C′ x) (pΨ (wk≈ asr sub-id asr sub-id o)) c₁)
         (λ η → 𝓖ₐ (𝓖ᵍ η))
         (λ {η} {η′} {C} {C′} e₁ x o (y , c₁) → VisQT-≈ x o y , Bc e₁ (Ctx-wkC C′ x) (pΨ (wk≈ asr sub-id asr sub-id o)) c₁)
         (gw (𝓖₂ 𝓖ᵗ) (λ {D} (x , c₁) → Kl-wk₂ x , c₁) (PsiH qH ok e p proj₂ proj₁ gt))
         (λ η → gw (𝓖₂ (𝓖ᵍ η)) (λ {D} (x , c₁) → Kl-wk₂ x , c₁) (PsiH qH ok e p proj₂ proj₁ (gg η)))
         (rwk (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt)) (λ η η′ d → rwk (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) (rg η η′ d)))
         (λ η h → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (m₁ η h)))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (mm η η′ h u))))
         (λ {D} (_ , c₁) → at≡ (run-wkC asr sub-id D (Ψ qH ok e p t₀)) {P = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dt c₁ G₁)))
         (λ η {D} (_ , c₁) → at≡ (run-wkC asr sub-id D (Ψ qH ok e p (g₁′ η))) {P = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dg η c₁ G₁)))
         (λ {D} (x₀ , c₁) → at≡ (run-wkC asr sub-id D (Ψ qH ok e p t₀)) {P = λ X → ∀ {C′ : Cx H t ((Fl ⊔ φ₀) ⊔ fk X) (Z* χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → VisQT-≈ x o x₀ , ch₀ c₁ G₁ (Ctx-wkC C′ x) (pΨ (wk≈ asr sub-id asr sub-id o))))
         (λ η {D} (x₀ , c₁) → at≡ (run-wkC asr sub-id D (Ψ qH ok e p (g₁′ η))) {P = λ X → ∀ {C′ : Cx H t ((Fl ⊔ φ₀) ⊔ fk X) (Z* χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → VisQT-≈ x o x₀ , chS η c₁ G₁ (Ctx-wkC C′ x) (pΨ (wk≈ asr sub-id asr sub-id o)))))
    where
    𝓖ₐ : ∀ {η} → ClT m _ (φ₀ ⊔ fk η) χ → ClT H t ((Fl ⊔ φ₀) ⊔ fk η) (Z* χ)
    𝓖ₐ 𝓖′ D = VisQT t D × 𝓖′ (pΨ qH ok e p (wkC asr sub-id D))
    𝓖₂ : ∀ {η} → ClT m _ (φ₀ ⊔ fk η) χ → ClT H t (Fl ⊔ (φ₀ ⊔ fk η)) (Z* χ)
    𝓖₂ 𝓖′ E = VisQT t E × 𝓖′ (pΨ qH ok e p E)
  PsiH {H = H} {m} {t = t} {φ = φ} {χ = χ} {w = w} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gcl {n = n} {q = q} {ψ = ψ} {s = s} {t = t₀} {h = g₁′} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) with tri n H
  ... | tlt l =
    gcl {ψ = Fl ⊔ ψ} (λ D → VisQT t D × 𝓖ᵗ (pΨ qH ok e p D)) (λ c → H₂ c , inc₁ (H₁ c)) 𝓖ₚ
       (λ {η} {η′} {C} {C′} e₁ x o (y , c₁) → VisQT-≈ x o y , Bc e₁ (Ctx-wkC C′ x) (pΨ (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) o)) c₁)
       (PsiH qH ok e p proj₂ proj₁ gt)
       (λ η → gw (λ D → VisQT t D × 𝓖ᵍ η (pΨ qH ok (e′ η) p D)) (λ {D} (x , c₁) → Kl-wk₂ x , c₁) (PsiH qH ok (e′ η) p proj₂ proj₁ (gg η)))
       (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) (λ η η′ d → rwk (R-Ψ qH ok (e′ η) p ok (e′ η′) p (≅ᴵ-refl _) (rg η η′ d)))
       (λ η h → wk-rᵗ (Ψ-congᵗ (m₁ η h))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (mm η η′ h u))))
       (λ (_ , c₁) G₁ r₁ → demFl r₁ (dt c₁ G₁))
       (λ η {D} (_ , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH ok (e′ η) p (g₁′ η))) {P = λ X → ∀ {K} (r₁ : InF K (Fl ⊔ ψ)) → Dem X r₁} (λ G₁ r₁ → demFl r₁ (dg η c₁ G₁)))
       (λ {D} (x₀ , c₁) G₁ {C′} x o → VisQT-≈ x o x₀ , ch₀ c₁ G₁ (Ctx-wkC C′ x) (pΨ (≈ᶜ-wkˡ (λ u → u) (AU _) o)))
       (λ η {D} (x₀ , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH ok (e′ η) p (g₁′ η))) {P = λ X → ∀ {C′ : Cx H t (Fl ⊔ φ) (upd (Z* χ) n ((Fl ⊔ ψ) ⊔ fk X))} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₚ X C′}
           (λ G₁ {C′} x o → VisQT-≈ x o x₀ , chS η c₁ G₁ (Ctx-wkC C′ x) (pΨ (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) o))))
    where
    e′ : ∀ η → Eh H m w (upd χ n (ψ ⊔ fk η))
    e′ η i h r = subst (Ev _) (sym (upd-gt χ _ (Hi-gt l h))) (e i h r)
    AU : ∀ η → Sub H (upd (κ Fl ∪ χ) n ((Fl ⊔ ψ) ⊔ fk η)) (κ Fl ∪ upd χ n (ψ ⊔ fk η))
    AU η = ⇑ (as-upd {κ Fl} {χ} n η)
    𝓖ₚ : ∀ η → ClT H t (Fl ⊔ φ) (upd (κ Fl ∪ χ) n ((Fl ⊔ ψ) ⊔ fk η))
    𝓖ₚ η D = VisQT t D × 𝓖ᵍ η (pΨ qH ok (e′ η) p (wkC (λ u → u) (AU η) D))
  ... | teq refl =
    gŝ 𝓑
       (λ {η} {η′} {O} eq (x , b) → x , λ d′ → Bc eq (Ctx-wkC O x) (pΨ (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) (ctxᶜ-refl O x))) (b (⊑ᴵ-≅ʳ d′ (≅ᴵ-sym eq))))
       (PsiH qH ok e p (λ c → inc₁ (H₁ c)) H₂ gt)
       (λ η d → gw (λ E → VisQT t E × 𝓖ᵍ η (pΨ qH (ok′ η d) (e′ η d) (p′ η d) E)) (λ {D} (c , (x , b)) → Kl-wk₂ (H₂ c) , b d) (PsiH qH (ok′ η d) (e′ η d) (p′ η d) proj₂ proj₁ (gg η)))
       (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt)
       (λ η d η′ d′ eη → rwk (R-Ψ qH (ok′ η d) (e′ η d) (p′ η d) (ok′ η′ d′) (e′ η′ d′) (p′ η′ d′) (≅ᴵ-refl _) (rg η η′ eη)))
       (λ η d → wk-rᵗ (Ψ-congᵗ (m₁ η (one⊑B B d))))
       (λ η d η′ d′ u → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (mm η η′ (one⊑B B d) u))))
       (λ {D} c G → bd⊑ B (rdT (H₂ c) proj₁ fc* (H0ᵀ rt (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t)))) G) (dt (inc₁ (H₁ c)) G))
       (λ {D} η d c (x , b) G → bd⊑ B (rdT (H₂ c) proj₁ fc* (wk-rᵀ (H0ᵀ (rg η η (≅ᴵ-refl η)) (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t))))) G)
            (at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH (ok′ η d) (e′ η d) (p′ η d) (g₁′ η))) {P = λ X → ∀ {K} (r₁ : InF K ψ) → Dem X r₁} (dg η (b d)) G))
       (λ {D} c G → cxQ (vQ (H₂ c)) , λ d → ch₀ (inc₁ (H₁ c)) G (Ctx-wkC D (cxQ (vQ (H₂ c)))) (pΨ (≈ᶜ-wkˡ _ _ (ctxᶜ-refl D (cxQ (vQ (H₂ c)))))))
       (λ {D} η d c (x , b) G → x , λ d′ → at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH (ok′ η d) (e′ η d) (p′ η d) (g₁′ η))) {P = λ X → ∀ (d₁ : Bd B ⊑ᴵ X) → 𝓖ᵍ X (pΨ qH (ok′ X d₁) (e′ X d₁) (p′ X d₁) (wkC (λ u → u) (AU X) D))}
            (λ G₁ d₁ → chS η (b d) G₁ (Ctx-wkC D x) (pΨ (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) (ctxᶜ-refl D x)))) G d′)
    where
    B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl) q)) p
    Lw : ∀ η → Bd B ⊑ᴵ η → Ht → Ordᴵ
    Lw η d = upd w n (Mlev (Fc B) (suc η) (FB B d))
    ok′ : ∀ η (d : Bd B ⊑ᴵ η) → Ok (Lw η d)
    ok′ η d = upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))
    e′ : ∀ η (d : Bd B ⊑ᴵ η) → Eh H m (Lw η d) (upd χ n (ψ ⊔ fk η))
    e′ η d i h r = upd-ev n i w χ (evη ψ B η d) (e i h r)
    p′ : ∀ η (d : Bd B ⊑ᴵ η) → t <ᴵ Lw η d H
    p′ η d = subst (t <ᴵ_) (sym (upd-self w n _)) (lim 0 (iF B))
    AU : ∀ η → Sub H (κ Fl ∪ χ) (κ Fl ∪ upd χ n (ψ ⊔ fk η))
    AU η i r u = proj₁ u , subst (Ev _) (sym (upd-lt χ _ r)) (proj₂ u)
    𝓑 : Ordᴵ → ClT H t (Fl ⊔ φ) (Z* χ)
    𝓑 η D = Ctxᶜ D × (∀ (d : Bd B ⊑ᴵ η) → 𝓖ᵍ η (pΨ qH (ok′ η d) (e′ η d) (p′ η d) (wkC (λ u → u) (AU η) D)))
  ... | tgt l =
    gŝ 𝓑
       (λ {η} {η′} {O} eq (x , b) → x , λ d′ → Bc eq (Ctx-wkC O x) (pΨ (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) (ctxᶜ-refl O x))) (b (⊑ᴵ-≅ʳ d′ (≅ᴵ-sym eq))))
       (PsiH qH ok e p (λ c → inc₁ (H₁ c)) H₂ gt)
       (λ η d → gw (λ E → VisQT t E × 𝓖ᵍ η (pΨ qH (ok′ η d) (e′ η d) (p′ η d) E)) (λ {D} (c , (x , b)) → Kl-wk₂ (H₂ c) , b d) (PsiH qH (ok′ η d) (e′ η d) (p′ η d) proj₂ proj₁ (gg η)))
       (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt)
       (λ η d η′ d′ eη → rwk (R-Ψ qH (ok′ η d) (e′ η d) (p′ η d) (ok′ η′ d′) (e′ η′ d′) (p′ η′ d′) (≅ᴵ-refl _) (rg η η′ eη)))
       (λ η d → wk-rᵗ (Ψ-congᵗ (m₁ η (one⊑B B d))))
       (λ η d η′ d′ u → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (mm η η′ (one⊑B B d) u))))
       (λ {D} c G → bd⊑ B (read1ᵀ D (cxQ (vQ (H₂ c))) _ (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) (H0ᵀ rt (𝟏⊑Ω̇ H t)) G) (dt (inc₁ (H₁ c)) G))
       (λ {D} η d c (x , b) G → bd⊑ B (read1ᵀ D x _ (rwk (R-Ψ qH (ok′ η d) (e′ η d) (p′ η d) (ok′ η d) (e′ η d) (p′ η d) (≅ᴵ-refl _) (rg η η (≅ᴵ-refl η)))) (wk-rᵀ (H0ᵀ (rg η η (≅ᴵ-refl η)) (𝟏⊑Ω̇ H t))) G)
            (at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH (ok′ η d) (e′ η d) (p′ η d) (g₁′ η))) {P = λ X → ∀ {K} (r₁ : InF K ψ) → Dem X r₁} (dg η (b d)) G))
       (λ {D} c G → cxQ (vQ (H₂ c)) , λ d → ch₀ (inc₁ (H₁ c)) G (Ctx-wkC D (cxQ (vQ (H₂ c)))) (pΨ (≈ᶜ-wkˡ _ _ (ctxᶜ-refl D (cxQ (vQ (H₂ c)))))))
       (λ {D} η d c (x , b) G → x , λ d′ → at≡ (run-wkC (λ u → u) (AU η) D (Ψ qH (ok′ η d) (e′ η d) (p′ η d) (g₁′ η))) {P = λ X → ∀ (d₁ : Bd B ⊑ᴵ X) → 𝓖ᵍ X (pΨ qH (ok′ X d₁) (e′ X d₁) (p′ X d₁) (wkC (λ u → u) (AU X) D))}
            (λ G₁ d₁ → chS η (b d) G₁ (Ctx-wkC D x) (pΨ (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) (ctxᶜ-refl D x)))) G d′)
    where
    B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l) q)) (zr ok n)
    Lw : ∀ η → Bd B ⊑ᴵ η → Ht → Ordᴵ
    Lw η d = upd w n (Mlev (Fc B) (suc η) (FB B d))
    ok′ : ∀ η (d : Bd B ⊑ᴵ η) → Ok (Lw η d)
    ok′ η d = upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))
    e′ : ∀ η (d : Bd B ⊑ᴵ η) → Eh H m (Lw η d) (upd χ n (ψ ⊔ fk η))
    e′ η d i h r = upd-ev n i w χ (evη ψ B η d) (e i h r)
    p′ : ∀ η (d : Bd B ⊑ᴵ η) → t <ᴵ Lw η d H
    p′ η d = subst (t <ᴵ_) (sym (upd-lt w _ l)) p
    AU : ∀ η → Sub H (κ Fl ∪ χ) (κ Fl ∪ upd χ n (ψ ⊔ fk η))
    AU η i r u = proj₁ u , subst (Ev _) (sym (upd-lt χ _ (tr< r l))) (proj₂ u)
    𝓑 : Ordᴵ → ClT H t (Fl ⊔ φ) (Z* χ)
    𝓑 η D = Ctxᶜ D × (∀ (d : Bd B ⊑ᴵ η) → 𝓖ᵍ η (pΨ qH (ok′ η d) (e′ η d) (p′ η d) (wkC (λ u → u) (AU η) D)))
  PsiH {H = H} {m} {t = t} {φ = φ} {χ = χ} {w = w} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gΩ↓ {n = n} {k = k₁} {q = q₁} {fe = fe} {ac = ac} {h = h} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) with tri n H
  ... | tlt l =
    gΩ↓ 𝓖₀′
       (λ ξ ζ {C} {C′} c₁ x o → VisQT-≈ x o (H₂ c₁) , inc₀ ξ ζ (H₁ c₁) (Ctx-wkC C′ x) (pΨ (≈ᶜ-wkˡ swp (λ i r′ → swp) o)))
       (λ ξ ζ D → W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D)))
       (λ ξ ζ {D} (x , c₀) u ru → subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))) u ≅ˢ runᶜ D (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ v))))) (sym (out-intoV l u))
           (subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru)))
       (λ 𝓔′ inc″ ξ ζ z rz₁ gz → subst (λ v → Gq g₂ H t (𝓔′ ξ ζ) (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ v))))) (sym (out-intoV l z))
          (gw (𝓖₅ 𝓔′ ξ ζ) (λ {D} c₁ → Kl-wk₂ (proj₁ (inc″ ξ ζ c₁)) , (D , c₁ , refl))
              (PsiH qH ok (e-lo ζ (inj₂ l) e) p proj₂ proj₁ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ z rz₁
                 (intoGV q₁ (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV l gz)))))))
       (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) nd →
          KlUp g₂ {D = D} cx′ (λ u → proj₁ (proj₂ u)) lc₃ (λ u → proj₁ (proj₂ u)) lc₃ (λ y ry →
             let Wp = wrap y ry
                 u = proj₁ Wp
                 ru = proj₁ (proj₂ Wp)
             in qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ u))) , wk-rᵀ (H0ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) u u ru) (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t)))) ,
                ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru))) x ,
          St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t₁ rt →
          let Wp = wrap (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p t₁)) (rwk (R-Ψ qH ok (e-lo ζ (inj₂ l) e) p ok (e-lo ζ (inj₂ l) e) p (≅ᴵ-refl _) rt))
          in proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))) (proj₁ Wp)) (sym (run-wkC swp (λ i r′ → swp) C′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p t₁))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (y , c₀) → VisQT-≈ x o y , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pΨ (wk≈ swp (λ i r′ → swp) swp (λ i r′ → swp) o)) c₀)
       (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ v))) ⊑ᵗ qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ′ (inj₂ l) e) p (h ξ′ ζ′ (intoV q₁ v′)))) (sym (out-intoV l z)) (sym (out-intoV l z′)) (wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm u)))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l₁ → subst₂ (λ v v′ → Rq H t t (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q₁ v)))) (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ′ (inj₂ l) e) p (h ξ′ ζ′ (intoV q₁ v′))))) (sym (out-intoV l z)) (sym (out-intoV l z′))
           (rwk (R-Ψ qH ok (e-lo ζ (inj₂ l) e) p ok (e-lo ζ′ (inj₂ l) e) p (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l₁))))
    where
    lc₃ : ∀ {ζ} → Sub H (lo n ζ ∪ Z* χ) (κ Fl)
    lc₃ i r′ u = proj₁ (proj₂ u)
    𝓖₀′ : ∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)
    𝓖₀′ ξ ζ D = VisQT t D × 𝓖₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo n ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pΨ qH ok (e-lo ζ (inj₂ l) e) p (wkC swp (λ i r′ → swp) D))
    𝓖₅ : (∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo n ζ ∪ Z* χ)) → ∀ ξ ζ → ClT H t (Fl ⊔ (ξ ⊔ φ)) (Z* (lo n ζ ∪ χ))
    𝓖₅ 𝓔′ ξ ζ E = VisQT t E × 𝓧₃ 𝓔′ ξ ζ (pΨ qH ok (e-lo ζ (inj₂ l) e) p E)
  ... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q₁)) p
  ...   | injᵃ (via d s) =
    gΩ 𝓖₀′
       (λ ξ ζ {C} {C′} c₁ x o → VisQT-≈ x o (H₂ c₁) , inc₀ ξ ζ (H₁ c₁) (Ctx-wkC C′ x) (pΨ (≈ᶜ-wkˡ swp (λ i r′ → swp) o)))
       (λ ξ ζ D → ptr⁻ d (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))))
       (λ ξ ζ {D} (x , c₀) u ru →
          subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))) (tr⁻Q d u) ≅ˢ runᶜ D (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d v)))))) (sym (out-intoU (<→◃ s) u))
                (subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))) (tr⁻Q d u) ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d u))))) (Wf ξ ζ c₀ (tr⁻Q d u) (R-tr⁻₂ d d ru))))
       (λ 𝓔′ inc″ ξ ζ z rz₁ gz →
          subst (λ v → Gq g₂ H t (𝓔′ ξ ζ) (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d v)))))) (sym (out-intoU (<→◃ s) z))
          (gw (𝓖₅ 𝓔′ ξ ζ) (λ {D} c₁ → Kl-wk₂ (proj₁ (inc″ ξ ζ c₁)) , (D , c₁ , refl))
              (PsiH qH ok (e-lo ζ (inj₁ refl) e) p proj₂ proj₁ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ (tr⁻Q d z) (R-tr⁻₂ d d rz₁)
                 (intoGV q₁ (Tr⁻ᵀ d {𝓧 = (λ D → ptr⁻ d (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D)))) ⟪ 𝓔′ ξ ζ ⟫ᵀ} (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , ptr⁻ o }) proj₁ (outG (<→◃ s) gz)))))))
       (λ ξ ζ (x , c₀) → Kl-ptr⁻ g₂ d (Wv ξ ζ c₀))
       (λ ξ ζ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) nd →
          KlUp g₂ {D = D} cx′ (λ u → proj₁ (proj₂ u)) lc₃ (λ u → proj₁ (proj₂ u)) lc₃ (λ y ry →
             let Wp = wrap y ry
                 u = proj₁ Wp
                 ru = proj₁ (proj₂ Wp)
             in qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d u)))) , wk-rᵀ (H0ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ (R-tr⁻₂ d d ru)) (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t)))) ,
                ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (subst (λ v → runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))) (tr⁻Q d u) ≅ˢ v) (run-wkC swp (λ i r′ → swp) D (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d u))))) (Wf ξ ζ c₀ (tr⁻Q d u) (R-tr⁻₂ d d ru)))) x ,
          St ξ ζ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t₁ rt →
          let Wp = wrap (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p t₁)) (rwk (R-Ψ qH ok (e-lo ζ (inj₁ refl) e) p ok (e-lo ζ (inj₁ refl) e) p (≅ᴵ-refl _) rt))
          in tr⁻Q d (proj₁ Wp) , R-tr⁻₂ d d (proj₁ (proj₂ Wp)) , FlΩ̇-tr⁻ d (proj₁ (proj₂ (proj₂ Wp))) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))) (tr⁻Q d (proj₁ Wp))) (sym (run-wkC swp (λ i r′ → swp) C′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p t₁))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (y , c₀) → VisQT-≈ x o y , cg ξ ξ′ ζ ζ′ (Ctx-wkC C x) (pΨ (wk≈ swp (λ i r′ → swp) swp (λ i r′ → swp) o)) c₀)
       (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d v)))) ⊑ᵗ qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ′ (inj₁ refl) e) p (h ξ′ ζ′ (intoV q₁ (tr⁻Q d v′))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
          (wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (tr⁻ᵗ-cong {e = d} {e′ = d} u))))))
       (λ ξ ξ′ ζ ζ′ d₁ dc z z′ l₁ → subst₂ (λ v v′ → Rq H t t (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q₁ (tr⁻Q d v))))) (qwk swp (λ i r′ → swp) (Ψ qH ok (e-lo ζ′ (inj₁ refl) e) p (h ξ′ ζ′ (intoV q₁ (tr⁻Q d v′)))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
          (rwk (R-Ψ qH ok (e-lo ζ (inj₁ refl) e) p ok (e-lo ζ′ (inj₁ refl) e) p (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d₁ dc _ _ (R-tr⁻₂ d d l₁)))))
    where
    lc₃ : ∀ {ζ} → Sub H (lo H ζ ∪ Z* χ) (κ Fl)
    lc₃ i r′ u = proj₁ (proj₂ u)
    𝓖₀′ : ∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo H ζ ∪ Z* χ)
    𝓖₀′ ξ ζ D = VisQT t D × 𝓖₀ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo H ζ ∪ Z* χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo H ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pΨ qH ok (e-lo ζ (inj₁ refl) e) p (wkC swp (λ i r′ → swp) D))
    𝓖₅ : (∀ ξ ζ → ClT H t (ξ ⊔ (Fl ⊔ φ)) (lo H ζ ∪ Z* χ)) → ∀ ξ ζ → ClT H t (Fl ⊔ (ξ ⊔ φ)) (Z* (lo H ζ ∪ χ))
    𝓖₅ 𝓔′ ξ ζ E = VisQT t E × 𝓧₃ 𝓔′ ξ ζ (pΨ qH ok (e-lo ζ (inj₁ refl) e) p E)
  ...   | injᵇ _ =
    gl (λ i → gw 𝓖₇ (λ {C} c₁ → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (H₂ c₁) , inc₀ ξ* Z₁ (H₁ c₁) (Ctx-wkC C (cxQ (vQ (H₂ c₁)))) (pΨ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (⇑ (cv* n)) (ctxᶜ-refl C (cxQ (vQ (H₂ c₁)))))))
                 (PsiH qH ok (e⁺ H ok e) p {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i)))))
       (λ i → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i)))))
    where
    ξ* = Fl ⊔ φ
    Z₁ = Z* χ
    f : Q n k₁ ξ* Z₁ → Q n k₁ ξ* Z₁
    f z = qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (h ξ* Z₁ (intoV q₁ z)))
    zt : ℕ → Q n k₁ ξ* Z₁
    zt = chainᵠ proj₁ fc* f
    𝓖₆ : ClT n k₁ (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₆ E = VisQT k₁ E × 𝓖₀ ξ* Z₁ (pΨ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) E)
    𝓖₇ : ClT H t (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₇ E = VisQT t E × 𝓖₀ ξ* Z₁ (pΨ qH ok (e⁺ H ok e) p E)
    zG : ∀ i → Gq g₂ n k₁ (W₀ ξ* Z₁ ⟪ 𝓖₀ ξ* Z₁ ⟫ᵀ) (zt i)
    zG zero = gw (KQ g₂ k₁) (λ {D} (x , C , c₁ , o) → vQ (Kl-wk₂ {le = proj₁} {lc = fc*} (VisQT-≈ x o (Wv ξ* Z₁ c₁)))) (Ω̇G g₂ n k₁)
    zG (suc i) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (VisQT-≈ x o (Wv ξ* Z₁ c₁)) , St ξ* Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁) , rwk (R-Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (H0ᵀ rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* Z₁ C) (qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁))) (sym (run-wkC dupr2 (⇑ (cv* n)) D (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁))) (runᶜ-≅ o (rwk (R-Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (PsiH q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i))))
    zm : ∀ i → zt i ⊑ᵗ zt (suc i)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ n (≅ᴵ-refl k₁))) (H0ᵀ (rf ξ* ξ* Z₁ Z₁ (∼ᶠ-refl ξ*) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl k₁))))))
    zm (suc i) = wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i))))
  ...   | injᶜ _ =
    gl (λ i → gw 𝓖₇ (λ {C} c₁ → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (H₂ c₁) , inc₀ ξ* Z₁ (H₁ c₁) (Ctx-wkC C (cxQ (vQ (H₂ c₁)))) (pΨ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (⇑ (cv* n)) (ctxᶜ-refl C (cxQ (vQ (H₂ c₁)))))))
                 (PsiH qH ok (e⁺ H ok e) p {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i)))))
       (λ i → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i)))))
    where
    ξ* = Fl ⊔ φ
    Z₁ = Z* χ
    f : Q n k₁ ξ* Z₁ → Q n k₁ ξ* Z₁
    f z = qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (h ξ* Z₁ (intoV q₁ z)))
    zt : ℕ → Q n k₁ ξ* Z₁
    zt = chainᵠ proj₁ fc* f
    𝓖₆ : ClT n k₁ (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₆ E = VisQT k₁ E × 𝓖₀ ξ* Z₁ (pΨ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) E)
    𝓖₇ : ClT H t (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₇ E = VisQT t E × 𝓖₀ ξ* Z₁ (pΨ qH ok (e⁺ H ok e) p E)
    zG : ∀ i → Gq g₂ n k₁ (W₀ ξ* Z₁ ⟪ 𝓖₀ ξ* Z₁ ⟫ᵀ) (zt i)
    zG zero = gw (KQ g₂ k₁) (λ {D} (x , C , c₁ , o) → vQ (Kl-wk₂ {le = proj₁} {lc = fc*} (VisQT-≈ x o (Wv ξ* Z₁ c₁)))) (Ω̇G g₂ n k₁)
    zG (suc i) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (VisQT-≈ x o (Wv ξ* Z₁ c₁)) , St ξ* Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁) , rwk (R-Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (H0ᵀ rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* Z₁ C) (qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁))) (sym (run-wkC dupr2 (⇑ (cv* n)) D (Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) t₁))) (runᶜ-≅ o (rwk (R-Ψ q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (PsiH q₁ ok (e⁺ n ok e) (ac (e n (inj₁ refl) q₁)) {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i))))
    zm : ∀ i → zt i ⊑ᵗ zt (suc i)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ n (≅ᴵ-refl k₁))) (H0ᵀ (rf ξ* ξ* Z₁ Z₁ (∼ᶠ-refl ξ*) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl k₁))))))
    zm (suc i) = wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i))))
  PsiH {H = H} {m} {t = t} {φ = φ} {χ = χ} {w = w} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gΩ↓ {n = n} {k = k₁} {q = q₁} {fe = fe} {ac = ac} {h = h} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) | tgt l =
    gl (λ i → gw 𝓖₇ (λ {C} c₁ → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (H₂ c₁) , inc₀ ξ* Z₁ (H₁ c₁) (Ctx-wkC C (cxQ (vQ (H₂ c₁)))) (pΨ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (⇑ (cv* n)) (ctxᶜ-refl C (cxQ (vQ (H₂ c₁)))))))
                 (PsiH qH ok (e⁺ n ok e) p {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i)))))
       (λ i → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i)))))
    where
    ξ* = Fl ⊔ φ
    Z₁ = Z* χ
    f : Q n k₁ ξ* Z₁ → Q n k₁ ξ* Z₁
    f z = qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) (h ξ* Z₁ (intoV q₁ z)))
    zt : ℕ → Q n k₁ ξ* Z₁
    zt = chainᵠ proj₁ fc* f
    𝓖₆ : ClT n k₁ (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₆ E = VisQT k₁ E × 𝓖₀ ξ* Z₁ (pΨ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) E)
    𝓖₇ : ClT H t (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₇ E = VisQT t E × 𝓖₀ ξ* Z₁ (pΨ qH ok (e⁺ n ok e) p E)
    zG : ∀ i → Gq g₂ n k₁ (W₀ ξ* Z₁ ⟪ 𝓖₀ ξ* Z₁ ⟫ᵀ) (zt i)
    zG zero = gw (KQ g₂ k₁) (λ {D} (x , C , c₁ , o) → vQ (Kl-wk₂ {le = proj₁} {lc = fc*} (VisQT-≈ x o (Wv ξ* Z₁ c₁)))) (Ω̇G g₂ n k₁)
    zG (suc i) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* n)} (VisQT-≈ x o (Wv ξ* Z₁ c₁)) , St ξ* Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) t₁) , rwk (R-Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (H0ᵀ rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* Z₁ C) (qwk dupr2 (⇑ (cv* n)) (Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) t₁))) (sym (run-wkC dupr2 (⇑ (cv* n)) D (Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) t₁))) (runᶜ-≅ o (rwk (R-Ψ q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (PsiH q₁ ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q₁)) {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoGV q₁ (zG i))))
    zm : ∀ i → zt i ⊑ᵗ zt (suc i)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ n (≅ᴵ-refl k₁))) (H0ᵀ (rf ξ* ξ* Z₁ Z₁ (∼ᶠ-refl ξ*) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl k₁))))))
    zm (suc i) = wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i))))
  PsiH {g} {H} {m} {t = t} {φ = φ} {χ = χ} {w = w} qH ok e p {𝓖 = 𝓖} {𝓧 = 𝓧} H₁ H₂ (gΩ {k = k₁} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gl (λ i → gw 𝓖₇ (λ {C} c₁ → Kl-wk₂ {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* m)} (H₂ c₁) , inc₀ ξ* Z₁ (H₁ c₁) (Ctx-wkC C (cxQ (vQ (H₂ c₁)))) (pΨ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (⇑ (cv* m)) (ctxᶜ-refl C (cxQ (vQ (H₂ c₁)))))))
                 (PsiH qH ok (e⁺ m ok e) p {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoG (<→◃ r) (zG i)))))
       (λ i → wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i)))))
    where
    ξ* = Fl ⊔ φ
    Z₁ = Z* χ
    f : Q m k₁ ξ* Z₁ → Q m k₁ ξ* Z₁
    f z = qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h ξ* Z₁ (intoU (<→◃ r) z)))
    zt : ℕ → Q m k₁ ξ* Z₁
    zt = chainᵠ proj₁ fc* f
    𝓖₆ : ClT m k₁ (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo m Z₁ ∪ χ))
    𝓖₆ E = KlT g k₁ E × 𝓖₀ ξ* Z₁ (pψ r E)
    𝓖₇ : ClT H t (Fl ⊔ (ξ* ⊔ φ)) (Z* (lo m Z₁ ∪ χ))
    𝓖₇ E = VisQT t E × 𝓖₀ ξ* Z₁ (pΨ qH ok (e⁺ m ok e) p E)
    zG : ∀ i → Gq (inp g) m k₁ (W₀ ξ* Z₁ ⟪ 𝓖₀ ξ* Z₁ ⟫ᵀ) (zt i)
    zG zero = gw (KQ (inp g) k₁) (λ {D} (x , C , c₁ , o) → K→Q g (Kl-wk g {le = proj₁} {lc = fc*} (KlT-≈ g x o (Wv ξ* Z₁ c₁)))) (Ω̇G g m k₁)
    zG (suc i) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk g {le = dupr2 {a = Fl} {b = φ}} {lc = ⇑ (cv* m)} (KlT-≈ g x o (Wv ξ* Z₁ c₁)) , St ξ* Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk dupr2 (⇑ (cv* m)) (ψᵠ r t₁) , rwk (R-ψᵠ r r (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (P0ᵀ {q = r} rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* Z₁ C) (qwk dupr2 (⇑ (cv* m)) (ψᵠ r t₁))) (sym (run-wkC dupr2 (⇑ (cv* m)) D (ψᵠ r t₁))) (runᶜ-≅ o (rwk (R-ψᵠ r r (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (Psi r {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ* Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) ξ* Z₁ (zt i) (G→R (zG i)) (intoG (<→◃ r) (zG i))))
    zm : ∀ i → zt i ⊑ᵗ zt (suc i)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ m (≅ᴵ-refl k₁))) (P0ᵀ {q = r} (rf ξ* ξ* Z₁ Z₁ (∼ᶠ-refl ξ*) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl k₁))))))
    zm (suc i) = wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = r} (hm (zm i))))
```
