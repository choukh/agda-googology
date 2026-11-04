> **机械克隆, 验收用.** 由 `LadderInfWAdd` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆, 验收用.** 由 `LadderInfAdd` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 加法

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFAdd](LadderNFAdd.lagda.md) 生成, 下面的说明是原文件的. `AddT.Add`: $W$ 在类 `𝓐` 里好, 类对压在 $W$ 之上封闭, 则 $W\boxplus y$ 好. 与 `OCF.Free.Add` 同形. `gcl` 行: 闭包的界多 $W$ 的第 $n$ 格地板, 由 `HonT` 给. 输出档位是 $W$ 的档位 $w=\mathrm{inp}\,g$: 和式的 `qs` 由 $W$ 担保 (`hqA`). 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderLabZInfWAdd (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.LadderLabZNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderLabZNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Align.LadderLabZNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderLabZNFWForce using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
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
open import OCF.Align.LadderLabZInfWClassF 𝕊 using (inp-map)
open import OCF.Align.LadderLabZInfWGood 𝕊
open import OCF.Align.LadderLabZInfWVis 𝕊
open RestrQ

Kl-cast : ∀ g′ w {m k φ χ} {D : Cx m k φ χ} → inp g′ ≡ w → KlT g′ k D → KlT w k D
Kl-cast g₀ g₀ refl v = v
Kl-cast g₁ g₂ refl v = v
Kl-cast g₂ g₂ refl v = v

cast-inp : ∀ g′ w → inp g′ ≡ w → inp w ≡ inp g′
cast-inp g₀ g₀ refl = refl
cast-inp g₁ g₂ refl = refl
cast-inp g₂ g₂ refl = refl

Kl-cast′ : ∀ g′ w {m k φ χ} {D : Cx m k φ χ} → inp g′ ≡ w → KlT g′ k D → KlT w k D
Kl-cast′ = Kl-cast

pr₁ᶜ : ∀ {m} {a b : Fv} → Sub m (a ∪ b) a
pr₁ᶜ i q = proj₁

module AddT {w m c α β} {𝓐 : ClT m c α β} {W : Q m c α β} (gW : Gq w m c 𝓐 W) (wW : WFl W)
            (cgA : ∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓐 C′ → 𝓐 C)
            (clA : ∀ {O₁ C″} → 𝓐 O₁ → FlOverᵀ W O₁ C″ → 𝓐 C″)
            (cxA : ∀ {C} → 𝓐 C → Ctxᶜ C)
            (hoA : ∀ {C} → 𝓐 C → HonT W C)
            (hqA : ∀ {C} → 𝓐 C → Hq w W C) where
  rW = WFl.rW wW

  wa : ∀ {φ χ} → Cx m c (α ⊔ φ) (β ∪ χ) → Cx m c α β
  wa D = wkC proj₁ pr₁ᶜ D

  𝓐𝓧 : ∀ {φ χ} → ClT m c φ χ → ClT m c (α ⊔ φ) (β ∪ χ)
  𝓐𝓧 𝓧 E = 𝓐 (wa E) × 𝓧 (pa W E)

  rW⊞ : ∀ {φ χ ψ ρ} {t : Q m c φ χ} {t′ : Q m c ψ ρ} → Rq m c c t t′ → Rq m c c (W ⊞ t) (W ⊞ t′)
  rW⊞ r = R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW r

  flW : ∀ {φ χ ψ ρ} {t : Q m c ψ ρ} {D : Cx m c (α ⊔ φ) (β ∪ χ)} {E : Cx m c (α ⊔ ψ) (β ∪ ρ)} → D ≈ᶜ E → Rq m c c t t → (G : Goodᴺ (toZ (runᶜ E (W ⊞ t)))) →
        Σ (Goodᴺ (toZ (runᶜ (wa D) W))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
  flW {D = D} o rt G = proj₁ J , ⊑-trans (proj₂ J) (proj₂ L)
    where
    L = B1ᵀ {x = qwk proj₁ pr₁ᶜ W} {W = W} rt (wk-lᵀ (R→⊑ᵀ rW)) o G
    J = pull≡ (run-wkC proj₁ pr₁ᶜ D W) (proj₁ L)

  ca : ∀ {φ χ} (D : Cx m c (α ⊔ φ) (β ∪ χ)) → 𝓐 (wa D) → Ctxᶜ D
  ca D x = Ctx-unwk D (cxA x)

  ra : ∀ {φ χ} (D : Cx m c (α ⊔ φ) (β ∪ χ)) → 𝓐 (wa D) → D ≈ᶜ D
  ra D x = ctxᶜ-refl D (ca D x)

  lv⊑ : ∀ {X : Ordˢ zero} {Y : Ordˢ zero} {G : Goodᴺ (toZ X)} {H : Goodᴺ (toZ Y)} → forceᴺ _ H ⊑ forceᴺ _ G → lvG H ⊑ᴵ lvG G
  lv⊑ {G = G} {H = H} h = toLevel-⊑ (forceᴺ-HS _ H) (forceᴺ-HS _ G) h

  hon⊞ : ∀ {ψ ρ} {y : Q m c ψ ρ} {D : Cx m c (α ⊔ ψ) (β ∪ ρ)} → 𝓐 (wa D) → Rq m c c y y → (G : Goodᴺ (toZ (runᶜ D (W ⊞ y)))) → Dm m (lvG G) α β
  hon⊞ {y = y} {D = D} c ry G =
    let N = flW (ra D c) ry G
    in (λ k → demUp k (lv⊑ {G = G} {H = proj₁ N} (proj₂ N)) (proj₁ (hoA c (proj₁ N)) k)) ,
       (λ i q k → demUp k (lv⊑ {G = G} {H = proj₁ N} (proj₂ N)) (proj₂ (hoA c (proj₁ N)) i q k))

  hq⊞ : ∀ w₁ → w₁ ≡ w → ∀ {ψ ρ} {y : Q m c ψ ρ} {D : Cx m c (α ⊔ ψ) (β ∪ ρ)} → 𝓐 (wa D) → Rq m c c y y → Hq w₁ (W ⊞ y) D
  hq⊞ g₀ E c ry = tt
  hq⊞ g₁ E c ry = tt
  hq⊞ g₂ refl {D = D} c ry G =
    let N = flW (ra D c) ry G
    in ⊑ᴵ-trans (hqA c (proj₁ N)) (lv⊑ {G = G} {H = proj₁ N} (proj₂ N))

  fo⊞ : ∀ {φ χ} {O₁ C″ : Cx m c (α ⊔ φ) (β ∪ χ)} {a : Q m c φ χ} → 𝓐 (wa O₁) → Rq m c c a a → FlOverᵀ (W ⊞ a) O₁ C″ → FlOverᵀ W (wa O₁) (wa C″)
  fo⊞ {O₁ = O₁} {C″ = C″} c ra₁ f′ = flo-overᵀ (Ctx-wkC C″ (cxoᵀ f′)) (λ t rt G →
    let J = pull≡ (sym (run-wkC proj₁ pr₁ᶜ C″ t)) G
        L = flwᵀ f′ (qwk proj₁ pr₁ᶜ t) (rwk rt) (proj₁ J)
        N = flW (ra O₁ c) ra₁ (proj₁ L)
    in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (proj₂ L) (proj₂ J)))

  Add : ∀ {g′} → inp g′ ≡ w → ∀ {φ χ} {𝓐₁ : ClT m c (α ⊔ φ) (β ∪ χ)} {𝓧 : ClT m c φ χ} {y : Q m c φ χ} → (∀ {C} → 𝓐₁ C → 𝓐 (wa C)) → (∀ {C} → 𝓐₁ C → 𝓧 (pa W C)) → Gq g′ m c 𝓧 y → Gq w m c 𝓐₁ (W ⊞ y)
  Add E inc H g0 = gw 𝓐 inc gW
  Add E inc H (gs {a = b} 𝓚 v k clk cgk ho hq) =
    gs (𝓐𝓧 𝓚) (λ c → inc c , v (H c)) (Add E proj₁ proj₂ k)
       (λ {O₁} {C″} (c , c₁) f′ nd →
         clA c (fo⊞ c (G→R k) f′) ,
         clk c₁ (flo-overᵀ (wW , cxoᵀ f′) (λ t rt G → flwᵀ f′ (W ⊞ t) (rW⊞ rt) G)) (ndg _ tt))
       (λ {C} {C′} x o (c , c₁) → cgA (Ctx-wkC C x) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ o) c , cgk (wW , x) (pa rW o) c₁)
       (λ {D} (c , c₁) G → (λ { (inl k₁) → proj₁ (hon⊞ c (G→R k) G) k₁ ; (inr k₁) → proj₁ (ho c₁ G) k₁ }) ,
                           (λ i q → λ { (inl k₁) → proj₂ (hon⊞ c (G→R k) G) i q k₁ ; (inr k₁) → proj₂ (ho c₁ G) i q k₁ }))
       (λ (c , c₁) → hq⊞ w refl c (G→R k))
  Add E inc H (gl f st) = gl (λ n → Add E inc H (f n)) (λ n → ⊞-congᵗ rW (st n))
  Add E {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gi {j = j} {f = f} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gi (𝓐𝓧 𝓖₀) (λ c → inc c , inc₀ (H c)) (λ D → W₀ (pa W D)) (λ (c , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez gz → Add E {𝓐₁ = 𝓔′} {𝓧 = λ F → Σ _ λ D → 𝓔′ D × (F ≡ pa W D)} (λ c → proj₁ (inc″ c)) (λ {D} c → D , c , refl)
          (hb (λ F → Σ _ λ D → 𝓔′ D × (F ≡ pa W D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , F , (D , c , refl) , o) → x , D , c , o })) gz)))
       (λ (c , c₀) → Wv c₀)
       (λ {D} {C′} (c , c₀) (aboveV cx′ wrap) nd →
         clA c (flo-overᵀ (Ctx-wkC C′ cx′) (λ t rt G →
           let J  = pull≡ (sym (run-wkC proj₁ pr₁ᶜ C′ t)) G
               Wp = wrap (qwk proj₁ pr₁ᶜ t) (rwk rt)
               u  = proj₁ Wp
               eu = proj₁ (proj₂ Wp)
               d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf c₀ u eu)
               dz = toZ-≅ d
               H₂ = Goodᴺ-tr dz (proj₁ J)
               N  = flW (ra D c) (rf eu) H₂
           in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dz) H₂ (proj₁ J))) (proj₂ J)))) ,
         St c₀ (aboveV (wW , cx′) (λ t rt → wrap (W ⊞ t) (rW⊞ rt))) (ndg _ tt))
       (λ {C} {C′} x o (c , c₀) → cgA (Ctx-wkC C x) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ o) c , cg (wW , x) (pa rW o) c₀)
       (λ h → ⊞-congᵗ rW (hm h)) (λ d → rW⊞ (rf d))
  Add E {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pa W D)) Bc (Add E inc H g₀′)
       (λ η e → Add E {𝓐₁ = λ D → 𝓐₁ D × 𝓑 η (pa W D)} {𝓧 = λ F → 𝓧 F × 𝓑 η F} (λ (c , b) → inc c) (λ (c , b) → H c , b) (gg η e))
       (rW⊞ et) (λ η e η′ e′ d → rW⊞ (eg η e η′ e′ d)) (λ η e → ⊞-congᵗ rW (m₁ η e)) (λ η e η′ e′ h → ⊞-congᵗ rW (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Add E inc H (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (rW⊞ r₁) (λ η e η′ e′ d → rW⊞ (r₂ η e η′ e′ d)) (Add E inc H go) (λ k → Add E inc H (gO k)) (⊞-congᵗ rW mo) (λ k → ⊞-congᵗ rW (mO k))
  Add E {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gw {le = le} {lc = lc} {x = x} 𝓖₁ inc₁ k) =
    gw (𝓐𝓧 𝓖₁) (λ {C} c → cgA (Ctx-wkC (wkC (λ e → proj₁ e , le (proj₂ e)) (λ i q e → proj₁ e , lc i q (proj₂ e)) C) (Ctx-wkC C (ca C (inc c)))) (≈ᶜ-wkˡ proj₁ pr₁ᶜ (≈ᶜ-wkˡ _ _ (≈ᶜ-wkʳ proj₁ pr₁ᶜ (ra C (inc c))))) (inc c) , inc₁ (H c)) (Add E proj₁ proj₂ k)
  Add E {φ = φ₀ ⊔ fk zero} {χ = χ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gclo {φ = φ₀} {t = t} {h = g} 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gw (𝓖ₐ 𝓖ᵗ) (λ {C} c →
           let cc = ca C (inc c)
               o₁ = ≈ᶜ-wkˡ asr (λ i q e → e) (≈ᶜ-wkˡ asl (λ i q e → e) (ctxᶜ-refl C cc))
           in cgA (Ctx-wkC (wkC asr (λ i q e → e) (wkC asl (λ i q e → e) C)) (Ctx-wkC (wkC asl (λ i q e → e) C) (Ctx-wkC C cc))) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ o₁) (inc c) ,
              cgᵗ (wW , Ctx-wkC (wkC asl (λ i q e → e) C) (Ctx-wkC C cc)) (pa rW o₁) (inc₁ (H c)))
       (gclo (𝓖ₐ 𝓖ᵗ) (λ c → c)
         (λ {C} {C′} x o (c , c₁) → cgA (Ctx-wkC (wkC asr (λ i q e → e) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ asr (λ i q e → e) asr (λ i q e → e) o)) c , cgᵗ (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr (λ i q e → e) asr (λ i q e → e) o)) c₁)
         (λ η → 𝓖ₐ (𝓖ᵍ η))
         (λ {η} {η′} {C} {C′} e x o (c , c₁) → cgA (Ctx-wkC (wkC asr (λ i q e₁ → e₁) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ asr (λ i q e₁ → e₁) asr (λ i q e₁ → e₁) o)) c , Bc e (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr (λ i q e₁ → e₁) asr (λ i q e₁ → e₁) o)) c₁)
         (gw (𝓐𝓧 𝓖ᵗ) (λ c → c) (Add E proj₁ proj₂ gt))
         (λ η → gw (𝓐𝓧 (𝓖ᵍ η)) (λ c → c) (Add E proj₁ proj₂ (gg η)))
         (rwk (rW⊞ rt)) (λ η η′ d → rwk (rW⊞ (rg η η′ d)))
         (λ η h → wk-lᵗ (wk-rᵗ (⊞-congᵗ rW (m₁ η h)))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (⊞-congᵗ rW (mm η η′ h u))))
         (λ {D} (c , c₁) → at≡ (run-wkC asr (λ i q e → e) D (W ⊞ t)) {P = λ X → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem X q} (dt⊔ {D = D} c (G→R gt) (dt c₁)))
         (λ η {D} (c , c₁) → at≡ (run-wkC asr (λ i q e → e) D (W ⊞ g η)) {P = λ X → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem X q} (dt⊔ {D = D} c (rg η η (≅ᴵ-refl η)) (dg η c₁)))
         (λ {D} (ca′ , c₁) → at≡ (run-wkC asr (λ i q e → e) D (W ⊞ t)) {P = λ X → ∀ {C′ : Cx m c ((α ⊔ φ₀) ⊔ fk X) (β ∪ χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → cgA (Ctx-wkC (wkC asr (λ i q e → e) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ asr (λ i q e → e) asr (λ i q e → e) o)) ca′ , ch₀ c₁ G₁ (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr (λ i q e → e) asr (λ i q e → e) o))))
         (λ η {D} (ca′ , c₁) → at≡ (run-wkC asr (λ i q e → e) D (W ⊞ g η)) {P = λ X → ∀ {C′ : Cx m c ((α ⊔ φ₀) ⊔ fk X) (β ∪ χ)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → cgA (Ctx-wkC (wkC asr (λ i q e → e) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ asr (λ i q e → e) asr (λ i q e → e) o)) ca′ , chS η c₁ G₁ (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr (λ i q e → e) asr (λ i q e → e) o)))))
    where
    𝓖ₐ : ∀ {η} → ClT m c (φ₀ ⊔ fk η) χ → ClT m c ((α ⊔ φ₀) ⊔ fk η) (β ∪ χ)
    𝓖ₐ 𝓖′ D = 𝓐 (wa (wkC asr (λ i q e → e) D)) × 𝓖′ (pa W (wkC asr (λ i q e → e) D))
    dt⊔ : ∀ {η} {D : Cx m c ((α ⊔ φ₀) ⊔ fk η) (β ∪ χ)} {y : Q m c (φ₀ ⊔ fk η) χ} → 𝓐 (wa (wkC asr (λ i q e → e) D)) → Rq m c c y y →
          ((G₁ : Goodᴺ (toZ (runᶜ (wkC asr (λ i q e → e) D) (W ⊞ y)))) → ∀ {K} (q : InF K φ₀) → Dem (lvG G₁) q) →
          (G₁ : Goodᴺ (toZ (runᶜ (wkC asr (λ i q e → e) D) (W ⊞ y)))) → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem (lvG G₁) q
    dt⊔ c ry ho G₁ (inl k) = proj₁ (hon⊞ c ry G₁) k
    dt⊔ c ry ho G₁ (inr k) = ho G₁ k
  Add E {φ = φ} {χ = χ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gcl {n = n} {q = q₁} {ψ = ψ} {t = t} {h = g} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
    gcl {ψ = β n ⊔ ψ} (𝓐𝓧 𝓖ᵗ) (λ c → inc c , inc₁ (H c)) (λ η → 𝓖ₚ (𝓖ᵍ η) η)
       (λ {η} {η′} {C} {C′} e x o (c , c₁) → cgA (Ctx-wkC (wkC (λ u → u) (AU η′) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) o)) c , Bc e (wW , Ctx-wkC C′ x) (pa rW (wk≈ (λ u → u) (AU η′) (λ u → u) (AU η) o)) c₁)
       (Add E proj₁ proj₂ gt)
       (λ η → gw (𝓐𝓧 (𝓖ᵍ η)) (λ c → c) (Add E proj₁ proj₂ (gg η)))
       (rW⊞ rt) (λ η η′ d → rwk (rW⊞ (rg η η′ d)))
       (λ η h → wk-rᵗ (⊞-congᵗ rW (m₁ η h))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (⊞-congᵗ rW (mm η η′ h u))))
       (λ {D} (c , c₁) G → λ { (inl k₁) → proj₂ (hon⊞ c (G→R gt) G) n q₁ k₁ ; (inr k₁) → dt c₁ G k₁ })
       (λ η {D} (c , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (W ⊞ g η)) {P = λ X → ∀ {K} (r : InF K (β n ⊔ ψ)) → Dem X r}
           (λ G₁ → λ { (inl k₁) → proj₂ (hon⊞ c (rg η η (≅ᴵ-refl η)) G₁) n q₁ k₁ ; (inr k₁) → dg η c₁ G₁ k₁ }))
       (λ {D} (c , c₁) G {C′} x o → cgA (Ctx-wkC (wkC (λ u → u) (AU _) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (≈ᶜ-wkˡ (λ u → u) (AU _) o)) c , ch₀ c₁ G (wW , Ctx-wkC C′ x) (pa rW (≈ᶜ-wkˡ (λ u → u) (AU _) o)))
       (λ η {D} (ca′ , c₁) → at≡ (run-wkC (λ u → u) (AU η) D (W ⊞ g η)) {P = λ X → ∀ {C′ : Cx m c (α ⊔ φ) (upd (β ∪ χ) n ((β n ⊔ ψ) ⊔ fk X))} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₚ (𝓖ᵍ X) X C′}
           (λ G₁ {C′} x o → cgA (Ctx-wkC (wkC (λ u → u) (AU _) C′) (Ctx-wkC C′ x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) o)) ca′ , chS η c₁ G₁ (wW , Ctx-wkC C′ x) (pa rW (wk≈ (λ u → u) (AU _) (λ u → u) (AU η) o))))
    where
    AU : ∀ η → Sub m (upd (β ∪ χ) n ((β n ⊔ ψ) ⊔ fk η)) (β ∪ upd χ n (ψ ⊔ fk η))
    AU η = ⇑ (as-upd {β} {χ} n η)
    𝓖ₚ : ∀ {η₀} → ClT m c φ (upd χ n (ψ ⊔ fk η₀)) → ∀ η → ClT m c (α ⊔ φ) (upd (β ∪ χ) n ((β n ⊔ ψ) ⊔ fk η₀))
    𝓖ₚ {η₀} 𝓖′ _ D = 𝓐 (wa (wkC (λ u → u) (AU η₀) D)) × 𝓖′ (pa W (wkC (λ u → u) (AU η₀) D))
  Add {g′} E {φ = φ} {χ = χ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gΩ↓ {n = n} {k = k₁} {q = q₁} {fe = fe} {h = h₀} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gΩ↓ 𝓖₀′
       (λ ξ ζ {C} {C′} c x o → cgA (Ctx-wkC (wkC swp (λ i r → swp) C′) (Ctx-wkC C′ x)) (≈ᶜ-wkˡ proj₁ pr₁ᶜ (≈ᶜ-wkʳ proj₁ pr₁ᶜ (≈ᶜ-wkˡ swp (λ i r → swp) o))) (inc c) ,
                              inc₀ ξ ζ (H c) (wW , Ctx-wkC C′ x) (pa rW (≈ᶜ-wkˡ swp (λ i r → swp) o)))
       (λ ξ ζ D → W₀ ξ ζ (pa W (wkC swp (λ i r → swp) D)))
       (λ ξ ζ {D} (c , c₀) u ru → subst (λ v → runᶜ (W₀ ξ ζ (pa W (wkC swp (λ i r → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r → swp) D (W ⊞ h₀ ξ ζ (intoV q₁ u))) (Wf ξ ζ c₀ u ru))
       (λ 𝓔′ inc″ ξ ζ z rz gz →
          gw (𝓐𝓧 (𝓧₃ 𝓔′ ξ ζ)) (λ {D} c → proj₁ (inc″ ξ ζ c) , (D , c , refl))
             (Add E proj₁ proj₂ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {F} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ ζ₁ c) }) ξ ζ z rz
                (intoGV q₁ (Gmono (λ { (x , F , (D , c , refl) , o) → x , D , c , o }) (outGV q₁ gz))))))
       (λ ξ ζ (c , c₀) → Wv ξ ζ c₀)
       (λ ξ ζ {D} {C′} (c , c₀) (aboveΩ cx′ wrap) nd →
          clA c (flo-overᵀ (Ctx-wkC (wkC swp (λ i r → swp) C′) (Ctx-wkC C′ cx′)) (λ t rt G →
            let J₁ = pull≡ (sym (run-wkC proj₁ pr₁ᶜ (wkC swp (λ i r → swp) C′) t)) G
                J₂ = pull≡ (sym (run-wkC swp (λ i r → swp) C′ (qwk proj₁ pr₁ᶜ t))) (proj₁ J₁)
                Wp = wrap (qwk swp (λ i r → swp) (qwk proj₁ pr₁ᶜ t)) (rwk (rwk rt))
                u  = proj₁ Wp
                ru = proj₁ (proj₂ Wp)
                d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf ξ ζ c₀ u ru)
                dz = toZ-≅ d
                H₂ = Goodᴺ-tr dz (proj₁ J₂)
                N  = flW (ra (wkC swp (λ i r → swp) D) c) (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) u u ru) H₂
            in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dz) H₂ (proj₁ J₂))) (⊑-trans (proj₂ J₂) (proj₂ J₁))))) ,
          St ξ ζ c₀ (aboveΩ (wW , Ctx-wkC C′ cx′) (λ t rt →
            let Wp = wrap (qwk swp (λ i r → swp) (W ⊞ t)) (rwk (rW⊞ rt)) in
            proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
            subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pa W (wkC swp (λ i r → swp) D))) (proj₁ Wp)) (sym (run-wkC swp (λ i r → swp) C′ (W ⊞ t))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (c , c₀) → cgA (Ctx-wkC (wkC swp (λ i r → swp) C) (Ctx-wkC C x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ swp (λ i r → swp) swp (λ i r → swp) o)) c , cg ξ ξ′ ζ ζ′ (wW , Ctx-wkC C x) (pa rW (wk≈ swp (λ i r → swp) swp (λ i r → swp) o)) c₀)
       (λ h → wk-lᵗ (wk-rᵗ (⊞-congᵗ rW (hm h))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rW⊞ (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    where
    𝓖₀′ : ∀ ξ ζ → ClT m c (ξ ⊔ (α ⊔ φ)) (lo n ζ ∪ (β ∪ χ))
    𝓖₀′ ξ ζ D = 𝓐 (wa (wkC swp (λ i r → swp) D)) × 𝓖₀ ξ ζ (pa W (wkC swp (λ i r → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT m c (ξ ⊔ (α ⊔ φ)) (lo n ζ ∪ (β ∪ χ))) → ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo n ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ F = Σ _ λ D → 𝓔′ ξ ζ D × (F ≡ pa W (wkC swp (λ i r → swp) D))
  Add {g′} E {φ = φ} {χ = χ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gΩ {k = k₁} {r = r} {h = h₀} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gΩ 𝓖₀′
       (λ ξ ζ {C} {C′} c x o → cgA (Ctx-wkC (wkC swp (λ i r₁ → swp) C′) (Ctx-wkC C′ x)) (≈ᶜ-wkˡ proj₁ pr₁ᶜ (≈ᶜ-wkʳ proj₁ pr₁ᶜ (≈ᶜ-wkˡ swp (λ i r₁ → swp) o))) (inc c) ,
                              inc₀ ξ ζ (H c) (wW , Ctx-wkC C′ x) (pa rW (≈ᶜ-wkˡ swp (λ i r₁ → swp) o)))
       (λ ξ ζ D → W₀ ξ ζ (pa W (wkC swp (λ i r₁ → swp) D)))
       (λ ξ ζ {D} (c , c₀) u ru → subst (λ v → runᶜ (W₀ ξ ζ (pa W (wkC swp (λ i r₁ → swp) D))) u ≅ˢ v) (run-wkC swp (λ i r₁ → swp) D (W ⊞ h₀ ξ ζ (intoU (<→◃ r) u))) (Wf ξ ζ c₀ u ru))
       (λ 𝓔′ inc″ ξ ζ z rz gz →
          gw (𝓐𝓧 (𝓧₃ 𝓔′ ξ ζ)) (λ {D} c → proj₁ (inc″ ξ ζ c) , (D , c , refl))
             (Add E proj₁ proj₂ (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {F} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ ζ₁ c) }) ξ ζ z rz
                (intoG (<→◃ r) (Gmono (λ { (x , F , (D , c , refl) , o) → x , D , c , o }) (subst (λ g₃ → Gq g₃ m k₁ _ z) (cast-inp g′ w E) (outG (<→◃ r) gz)))))))
       (λ ξ ζ (c , c₀) → Kl-cast′ g′ w E (Wv ξ ζ c₀))
       (λ ξ ζ {D} {C′} (c , c₀) (aboveΩ cx′ wrap) nd →
          clA c (flo-overᵀ (Ctx-wkC (wkC swp (λ i r₁ → swp) C′) (Ctx-wkC C′ cx′)) (λ t rt G →
            let J₁ = pull≡ (sym (run-wkC proj₁ pr₁ᶜ (wkC swp (λ i r₁ → swp) C′) t)) G
                J₂ = pull≡ (sym (run-wkC swp (λ i r₁ → swp) C′ (qwk proj₁ pr₁ᶜ t))) (proj₁ J₁)
                Wp = wrap (qwk swp (λ i r₁ → swp) (qwk proj₁ pr₁ᶜ t)) (rwk (rwk rt))
                u  = proj₁ Wp
                ru = proj₁ (proj₂ Wp)
                d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf ξ ζ c₀ u ru)
                dz = toZ-≅ d
                H₂ = Goodᴺ-tr dz (proj₁ J₂)
                N  = flW (ra (wkC swp (λ i r₁ → swp) D) c) (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) u u ru) H₂
            in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dz) H₂ (proj₁ J₂))) (⊑-trans (proj₂ J₂) (proj₂ J₁))))) ,
          St ξ ζ c₀ (aboveΩ (wW , Ctx-wkC C′ cx′) (λ t rt →
            let Wp = wrap (qwk swp (λ i r₁ → swp) (W ⊞ t)) (rwk (rW⊞ rt)) in
            proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
            subst (λ v → v ≅ˢ runᶜ (W₀ ξ ζ (pa W (wkC swp (λ i r₁ → swp) D))) (proj₁ Wp)) (sym (run-wkC swp (λ i r₁ → swp) C′ (W ⊞ t))) (proj₂ (proj₂ (proj₂ Wp))))) (ndg _ tt))
       (λ ξ ξ′ ζ ζ′ {C} {C′} x o (c , c₀) → cgA (Ctx-wkC (wkC swp (λ i r₁ → swp) C) (Ctx-wkC C x)) (wk≈ proj₁ pr₁ᶜ proj₁ pr₁ᶜ (wk≈ swp (λ i r₁ → swp) swp (λ i r₁ → swp) o)) c , cg ξ ξ′ ζ ζ′ (wW , Ctx-wkC C x) (pa rW (wk≈ swp (λ i r₁ → swp) swp (λ i r₁ → swp) o)) c₀)
       (λ h → wk-lᵗ (wk-rᵗ (⊞-congᵗ rW (hm h))))
       (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rW⊞ (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    where
    𝓖₀′ : ∀ ξ ζ → ClT m c (ξ ⊔ (α ⊔ φ)) (lo m ζ ∪ (β ∪ χ))
    𝓖₀′ ξ ζ D = 𝓐 (wa (wkC swp (λ i r₁ → swp) D)) × 𝓖₀ ξ ζ (pa W (wkC swp (λ i r₁ → swp) D))
    𝓧₃ : (∀ ξ ζ → ClT m c (ξ ⊔ (α ⊔ φ)) (lo m ζ ∪ (β ∪ χ))) → ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)
    𝓧₃ 𝓔′ ξ ζ F = Σ _ λ D → 𝓔′ ξ ζ D × (F ≡ pa W (wkC swp (λ i r₁ → swp) D))
  Add {g′} E inc H (gm zc rz₁ gx) = Add (trans (inp-eag g′) E) inc (λ c → H c , tt) gx
```
