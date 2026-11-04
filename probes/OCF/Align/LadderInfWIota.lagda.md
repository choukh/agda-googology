> **机械克隆, 验收用.** 由 `LadderInfIota` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 同层嵌入

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFIota](LadderNFIota.lagda.md) 生成, 下面的说明是原文件的. `Iota q : Gq g c 𝓧 x → Gq (eag g) d 𝓖 (ι q x)`, 只要 $C\in\mathcal G$ 推出 `pι q C` ∈ $\mathcal X$, 且 $C$ 的头不是 `ι↓` (`Nd`). 与 `OCF.Free.Tail` 的 `Iota` 同形, 多 `gcl`, `gΩ↓`, `gm` 三行. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfWIota (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderNFWForce using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfWTree 𝕊
open import OCF.Align.LadderInfWRel 𝕊
open import OCF.Align.LadderInfWCx 𝕊
open import OCF.Align.LadderInfWRules 𝕊
open import OCF.Align.LadderInfWRules2 𝕊
open import OCF.Align.LadderInfWRules3 𝕊
open import OCF.Align.LadderInfWStrict 𝕊
open import OCF.Align.LadderInfWStrict2 𝕊
open import OCF.Align.LadderInfWClass 𝕊
open import OCF.Align.LadderInfWClassF 𝕊 using (inp-map)
open import OCF.Align.LadderInfWGood 𝕊
open import OCF.Align.LadderInfWVis 𝕊
open RestrQ

Vι : ∀ {m c φ χ} → ClT m c φ χ
Vι D = Ctxᶜ D × Nd D

eag-idem : ∀ g → eag (eag g) ≡ eag g
eag-idem g₀ = refl
eag-idem g₁ = refl
eag-idem g₂ = refl

Kl-eag : ∀ g {m k φ χ} {D : Cx m k φ χ} → KlT g k D → KlT (eag g) k D
Kl-eag g₀ v = v
Kl-eag g₁ v = v
Kl-eag g₂ v = v

Iota : ∀ {g m c d φ χ} (q : c ◃ d) {𝓖 : ClT m d φ χ} {𝓧 : ClT m c φ χ} {x : Q m c φ χ} → (∀ {C} → 𝓖 C → 𝓧 (pι q C)) → (∀ {C} → 𝓖 C → Vι C) → Gq g m c 𝓧 x → Gq (eag g) m d 𝓖 (ι q x)
Iota q H H₂ g0 = g0
Iota {g} q H H₂ (gs 𝓚 v k clk cgk ho hq) =
  gs (λ D → Vι D × 𝓚 (pι q D)) (λ c → H₂ c , v (H c)) (Iota q proj₂ proj₁ k)
     (λ {O₁} {C″} ((x , n) , c₁) f nd₀ → (cxoᵀ f , ndE _ nd₀) , clk c₁ (flo-overᵀ (ndE _ nd₀ , cxoᵀ f) (λ t rt G → flwᵀ f (ι q t) (R-ι q q rt) G)) (ndg _ tt))
     (λ x o ((_ , n) , c₁) → (x , Nd-≈ o n) , cgk (Nd-≈ o n , x) (pι o) c₁)
     (λ (_ , c₁) G → ho c₁ G)
     (λ _ → Hq-eag g)
Iota q H H₂ (gl f st) = gl (λ n → Iota q H H₂ (f n)) (λ n → ι-congᵗ {q = q} (st n))
Iota q {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → Vι D × 𝓖₀ (pι q D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (pι q D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → Iota q {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pι q D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pι q D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) nd₀ → (cx′ , ndE _ nd₀) , St c₀ (aboveV (ndE _ nd₀ , cx′) (λ t rt → wrap (ι q t) (R-ι q q rt))) (ndg _ tt))
     (λ x o ((_ , n) , c₀) → (x , Nd-≈ o n) , cg (Nd-≈ o n , x) (pι o) c₀)
     (λ h → ι-congᵗ {q = q} (hm h)) (λ d → R-ι q q (rf d))
Iota q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (pι q D)) Bc (Iota q H H₂ g₀′)
     (λ η e → Iota q {𝓖 = λ D → 𝓖 D × 𝓑 η (pι q D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-ι q q et) (λ η e η′ e′ d → R-ι q q (eg η e η′ e′ d)) (λ η e → ι-congᵗ {q = q} (m₁ η e)) (λ η e η′ e′ u → ι-congᵗ {q = q} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Iota q H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-ι q q r₁) (λ η e η′ e′ d → R-ι q q (r₂ η e η′ e′ d)) (Iota q H H₂ go) (λ k → Iota q H H₂ (gO k)) (ι-congᵗ {q = q} mo) (λ k → ι-congᵗ {q = q} (mO k))
Iota q H H₂ (gw {le = le} {lc = lc} 𝓖₁ inc₁ k) =
  gw (λ E → Vι E × 𝓖₁ (pι q E)) (λ {C} c → (Ctx-wkC C (proj₁ (H₂ c)) , Nd-wk C (proj₂ (H₂ c))) , inc₁ (H c)) (Iota q proj₂ proj₁ k)
Iota q {𝓖 = 𝓖} H H₂ (gclo 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gclo (λ D → Vι D × 𝓖ᵗ (pι q D)) (λ c → H₂ c , inc₁ (H c)) (λ x o ((_ , n) , c₁) → (x , Nd-≈ o n) , cgᵗ (Nd-≈ o n , x) (pι o) c₁)
     (λ η D → Vι D × 𝓖ᵍ η (pι q D))
     (λ e x o ((_ , n) , c₁) → (x , Nd-≈ o n) , Bc e (Nd-≈ o n , x) (pι o) c₁)
     (Iota q proj₂ proj₁ gt) (λ η → Iota q proj₂ proj₁ (gg η))
     (R-ι q q rt) (λ η η′ e → R-ι q q (rg η η′ e))
     (λ η h → ι-congᵗ {q = q} (m₁ η h)) (λ η η′ h u → ι-congᵗ {q = q} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ ((_ , n) , c₁) G x o → (x , Nd-≈ o n) , ch₀ c₁ G (Nd-≈ o n , x) (pι o)) (λ η ((_ , n) , c₁) G x o → (x , Nd-≈ o n) , chS η c₁ G (Nd-≈ o n , x) (pι o))
Iota q {𝓖 = 𝓖} H H₂ (gcl 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gcl (λ D → Vι D × 𝓖ᵗ (pι q D)) (λ c → H₂ c , inc₁ (H c))
     (λ η D → Vι D × 𝓖ᵍ η (pι q D))
     (λ e x o ((_ , n) , c₁) → (x , Nd-≈ o n) , Bc e (Nd-≈ o n , x) (pι o) c₁)
     (Iota q proj₂ proj₁ gt) (λ η → Iota q proj₂ proj₁ (gg η))
     (R-ι q q rt) (λ η η′ e → R-ι q q (rg η η′ e))
     (λ η h → ι-congᵗ {q = q} (m₁ η h)) (λ η η′ h u → ι-congᵗ {q = q} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ ((_ , n) , c₁) G x o → (x , Nd-≈ o n) , ch₀ c₁ G (Nd-≈ o n , x) (pι o)) (λ η ((_ , n) , c₁) G x o → (x , Nd-≈ o n) , chS η c₁ G (Nd-≈ o n , x) (pι o))
Iota {m = m} {d = d} {φ = φ} {χ = χ} q {𝓖 = 𝓖} H H₂ (gΩ↓ {n = n} {k = k} {q = q₁} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ↓ (λ ξ ζ D → Vι D × 𝓖₀ ξ ζ (pι q D))
     (λ ξ ζ c x o → (x , Nd-≈ o (proj₂ (H₂ c))) , inc₀ ξ ζ (H c) (Nd-≈ o (proj₂ (H₂ c)) , x) (pι o))
     (λ ξ ζ D → W ξ ζ (pι q D))
     (λ ξ ζ (x , c₀) u ru → Wf ξ ζ c₀ u ru)
     (λ 𝓔′ inc″ ξ ζ z rz g →
        Iota q {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ ζ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ ζ₁ c) }) ξ ζ z rz
               (intoGV q₁ (Gmono (λ { (x , E , (D , c , refl) , o) → x , D , c , o }) (outGV q₁ g)))))
     (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
     (λ ξ ζ (x , c₀) (aboveΩ cx′ wrap) nd₀ → (cx′ , ndE _ nd₀) , St ξ ζ c₀ (aboveΩ (ndE _ nd₀ , cx′) (λ t rt → wrap (ι q t) (R-ι q q rt))) (ndg _ tt))
     (λ ξ ξ′ ζ ζ′ x o ((_ , n₀) , c₀) → (x , Nd-≈ o n₀) , cg ξ ξ′ ζ ζ′ (Nd-≈ o n₀ , x) (pι o) c₀)
     (λ u → ι-congᵗ {q = q} (hm u))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → R-ι q q (rf ξ ξ′ ζ ζ′ e dc z z′ l))
  where
  𝓧₃ : (∀ ξ ζ → ClT m d (ξ ⊔ φ) (lo n ζ ∪ χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo n ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pι q D)
Iota {g} {m = m} {c = c} {d = d} {φ = φ} {χ = χ} q {𝓖 = 𝓖} H H₂ (gΩ {k = k} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ (λ ξ ζ D → Vι D × 𝓖₀ ξ ζ (pι q D))
     (λ ξ ζ c₁ x o → (x , Nd-≈ o (proj₂ (H₂ c₁))) , inc₀ ξ ζ (H c₁) (Nd-≈ o (proj₂ (H₂ c₁)) , x) (pι o))
     (λ ξ ζ D → W ξ ζ (pι q D))
     (λ ξ ζ {D} (x , c₀) u ru → subst (λ v → runᶜ (W ξ ζ (pι q D)) u ≅ˢ runᶜ D (ι q (h ξ ζ (intoU (<→◃ r) v)))) (sym (out-intoU (<→◃ (<◃ r q)) u)) (Wf ξ ζ c₀ u ru))
     (λ 𝓔′ inc″ ξ ζ z rz gz → subst (λ v → Gq (eag g) m d (𝓔′ ξ ζ) (ι q (h ξ ζ (intoU (<→◃ r) v)))) (sym (out-intoU (<→◃ (<◃ r q)) z))
        (Iota q {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c₁ → D , c₁ , refl) (λ c₁ → proj₁ (inc″ ξ ζ c₁))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ z rz
               (intoG (<→◃ r) (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (subst (λ g′ → Gq g′ m k _ z) (inp-eag g) (outG (<→◃ (<◃ r q)) gz)))))))
     (λ ξ ζ (x , c₀) → Kl-eag g (Wv ξ ζ c₀))
     (λ ξ ζ (x , c₀) (aboveΩ cx′ wrap) nd₀ → (cx′ , ndE _ nd₀) , St ξ ζ c₀ (aboveΩ (ndE _ nd₀ , cx′) (λ t rt → wrap (ι q t) (R-ι q q rt))) (ndg _ tt))
     (λ ξ ξ′ ζ ζ′ x o ((_ , n₀) , c₀) → (x , Nd-≈ o n₀) , cg ξ ξ′ ζ ζ′ (Nd-≈ o n₀ , x) (pι o) c₀)
     (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → ι q (h ξ ζ (intoU (<→◃ r) v)) ⊑ᵗ ι q (h ξ′ ζ′ (intoU (<→◃ r) v′))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ r q)) z′)) (ι-congᵗ {q = q} (hm u)))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → subst₂ (λ v v′ → Rq m d d (ι q (h ξ ζ (intoU (<→◃ r) v))) (ι q (h ξ′ ζ′ (intoU (<→◃ r) v′)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ r q)) z′)) (R-ι q q (rf ξ ξ′ ζ ζ′ e dc z z′ l)))
  where
  𝓧₃ : (∀ ξ ζ → ClT m d (ξ ⊔ φ) (lo m ζ ∪ χ)) → ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ pι q D)
Iota {g} {m = m} {d = d} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gm zc rz₁ gx) =
  subst (λ g′ → Gq g′ m d 𝓖 _) (eag-idem g) (Iota q {𝓖 = 𝓖} {𝓧 = λ C → 𝓧 C × Nd C} (λ c → H c , tt) H₂ gx)
```
