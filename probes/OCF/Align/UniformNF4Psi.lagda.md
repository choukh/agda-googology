# 数据树上的无符号闭包定理 (八): $\psi_{\Omega+t}$ 的闭包定理

> 接 [UniformNF4Add](UniformNF4Add.lagda.md). 结论先说:
>
> 1. **`PsiM.Psi q : Gᵀ c 𝓧 x → Gᵀ t 𝓖 (ψᵒ q x)`, 只要 $C\in\mathcal G$ 推出 `pψ q C` ∈ $\mathcal X$.** 对一切 $t<c$, 一切类, 没有对 $c$ 或 $t$ 的归纳. 这是 [Uniform4Psi](Uniform4Psi.lagda.md) `Ld-ψ` 的记号无关形式, 行与行一一对应, 证明里没有标签.
> 2. **后继行就是 `clk`.** $\psi(a+1)=\lim\mathrm{rep}\,X$, $\mathrm{rep}(n+2)=\mathrm{rep}(n+1)\oplus X$. 第 $n+2$ 份的 $X$ 在上下文 `pψ q (pa W …)` 下; 它压在 $X$ 之上, 因为 $X\sqsubseteq W\oplus\psi(t)$ (`Xfl`, `B1ᵀ`). 所以吸收者就是 `FlOverᵀ` 一条, **没有 "底抬高"**: 底就是上下文的一部分, 被量化了.
> 3. **`oΩ` 的两行.** 穿透 (`pen`): 把类沿 `pψ q` 拉回. 折叠 (`chain`): `zG` 对 $n$ 归纳, 第 $n+1$ 个链点是 $\psi_r$ 作用在第 $n$ 个上, 它的上下文压在 `W` 之上 (`St`, `P0ᵀ`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Psi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (≅ᶻ-sym; _≅ˢ_; z≅; ≅ˢ-trans; toZ-≅)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; ⊔∼; flo; cvFlo)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base
open import OCF.Align.UniformNF4Base
open import OCF.Align.UniformNF4Rules
open import OCF.Align.UniformNF4Strict
open import OCF.Align.UniformNF4Class
open import OCF.Align.UniformNF4ClassF using (inp-map)
open import OCF.Align.UniformNF4Good
open import OCF.Align.UniformNF4Add

demFl : ∀ {K X φ} (q : InF K (Fl ⊔ φ)) → (∀ {K′} (k : InF K′ φ) → Dem X k) → Dem X q
demFl (inl (inr ink)) h = inj₂ z≅
demFl (inr k) h = h k

module PsiM (Ω̇G : ∀ t → Gᵀ t {Fl} 𝓥 (Ω̇ t)) where
  Psi : ∀ {c t φ} (q : t <ᴸ c) {𝓖 : ClT t (Fl ⊔ φ)} {𝓧 : ClT c φ} {x : O c φ} → (∀ {C} → 𝓖 C → 𝓧 (pψ q C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gᵀ c 𝓧 x → Gᵀ t 𝓖 (ψᵒ q x)
  PsiΩ : ∀ {c t φ m} (q : t <ᴸ c) {𝓖 : ClT t (Fl ⊔ φ)} {𝓧 : ClT c φ} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {r : m <ᴸ c} {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} →
         (∀ {C} → 𝓖 C → 𝓧 (pψ q C)) → (∀ {C} → 𝓖 C → 𝓥 C) →
         (𝓖₀ : ∀ ξ → ClT c (ξ ⊔ φ)) →
         (∀ ξ {C} {C′ : Cx c (ξ ⊔ φ)} → 𝓧 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ C′) →
         (W : ∀ ξ → Cx c (ξ ⊔ φ) → Cx m ξ) →
         (∀ ξ {C} → 𝓖₀ ξ C → ∀ (u : O m ξ) → Rᵒ m u u → runᶜ (W ξ C) u ≅ˢ runᶜ C (h ξ (intoU r u))) →
         (∀ (𝓔 : ∀ ξ → ClT c (ξ ⊔ φ)) → (∀ ξ {C} → 𝓔 ξ C → 𝓖₀ ξ C) → ∀ ξ (z : O m ξ) → Rᵒ m z z → LG c r (W ξ ⟪ 𝓔 ξ ⟫ᵀ) z → Gᵀ c (𝓔 ξ) (h ξ (intoU r z))) →
         (∀ ξ {C} → 𝓖₀ ξ C → 𝓥 (W ξ C)) →
         LG c r {Fl} 𝓥 (Ω̇ m) →
         (∀ ξ {C} {C′ : Cx c (ξ ⊔ φ)} → 𝓖₀ ξ C → AboveΩ C′ (W ξ C) → 𝓖₀ ξ C′) →
         (∀ ξ ξ′ {C : Cx c (ξ ⊔ φ)} {C′ : Cx c (ξ′ ⊔ φ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ C′ → 𝓖₀ ξ C) →
         (∀ {ξ ξ′} {z : O m ξ} {z′ : O m ξ′} → z ⊑ᵗ z′ → h ξ (intoU r z) ⊑ᵗ h ξ′ (intoU r z′)) →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O m ξ) (z′ : O m ξ′) → Rᵒ m z z′ → Rᵒ c (h ξ (intoU r z)) (h ξ′ (intoU r z′))) →
         (p : Pen m t) → Gᵀ t 𝓖 (ψᵒΩ q fe r h p)

  Psi {t = t} q H H₂ g0 = gw 𝓥 (λ {C} c → Ctx-wkC C (H₂ c)) (Ω̇G t)
  Psi {c = c} {t = t} {φ = φ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gs {a = a} 𝓚 v g clk cgk ho) =
    gl (λ n → Gmono (λ c₁ → H₂ c₁ , v (H c₁)) (rep-good n)) mono
    where
    𝓐 : ClT t (Fl ⊔ φ)
    𝓐 C = 𝓥 C × 𝓚 (pψ q C)
    X = ψᵒ q a
    gX : Gᵀ t 𝓐 X
    gX = Psi q proj₂ proj₁ g
    ra = G→R g
    rX : Rᵒ t X X
    rX = R-ψ q q ra
    Xfl : ∀ n → X ⊑ᵀ repᵒ X (suc n)
    Xfl zero = R→⊑ᵀ rX
    Xfl (suc n) = wk-rᵀ (B1ᵀ rX (Xfl n))
    rR : ∀ n → Rᵒ t (repᵒ X n) (repᵒ X n)
    rR n = R-rep (∼ᶠ-refl _) rX n
    wf : ∀ n → WFl (repᵒ X (suc n))
    wf n = wfl (rR (suc n)) (⊑ᵀ-trans (P0ᵀ {q = q} ra (𝟏⊑Ω̇ t)) (Xfl n))
    clA : ∀ n {O₁ C″} → 𝓐 O₁ → FlOverᵀ (repᵒ X (suc n)) O₁ C″ → 𝓐 C″
    clA n {O₁} {C″} (x , c₁) f = cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t₁ rt G →
      let L = flwᵀ f (ψᵒ q t₁) (R-ψ q q rt) G
          N = Xfl n (ctxᶜ-refl O₁ x) (proj₁ L)
      in proj₁ N , ⊑-trans (proj₂ N) (proj₂ L)))
    hoA : ∀ n {C} → 𝓐 C → HonT (repᵒ X (suc n)) C
    hoA n {C} (x , c₁) G q₁ = demFl q₁ (λ k →
      let N = Xfl n (ctxᶜ-refl C x) G
      in demUp k (toLevel-⊑ (forceᴺ-HS _ (proj₁ N)) (forceᴺ-HS _ G) (proj₂ N)) (ho c₁ (proj₁ N) k))
    press : ∀ n {C} → 𝓐 C → 𝓐 (pa (repᵒ X (suc n)) (wkC (λ e → e , e) C))
    press n {C} (x , c₁) = (wf n , Ctx-wkC C x) , clk c₁ (flo-overᵀ (wf n , Ctx-wkC C x) (λ t₁ rt G →
      B1ᵀ {x = X} {W = repᵒ X (suc n)} (R-ψ q q rt) (Xfl n) (≈ᶜ-wkʳ (λ e → e , e) (ctxᶜ-refl C x)) G))
    dup-id : ∀ (C : Cx t (Fl ⊔ φ)) → wkC proj₁ (wkC (λ e → e , e) C) ≡ C
    dup-id C = trans (wkC-comp proj₁ (λ e → e , e) C) (wkC-id C)
    rep-good : ∀ n → Gᵀ t 𝓐 (repᵒ X n)
    rep-good zero = g0
    rep-good (suc zero) = gX
    rep-good (suc (suc n)) =
      gw (λ E → 𝓐 (wkC proj₁ E) × 𝓐 (pa (repᵒ X (suc n)) E))
         (λ {C} c₁ → subst 𝓐 (sym (dup-id C)) c₁ , press n c₁)
         (AddT.Add {W = repᵒ X (suc n)} (rep-good (suc n)) (wf n)
                   (λ x o (_ , c₁) → x , cgk x (pψ o) c₁) (clA n) proj₁ (hoA n)
                   {𝓐₁ = λ E → 𝓐 (wkC proj₁ E) × 𝓐 (pa (repᵒ X (suc n)) E)} {𝓧 = 𝓐} proj₁ proj₂ gX)
    mono : ∀ n → repᵒ X n ⊑ᵗ repᵒ X (suc n)
    mono zero = ⊑ᵀ→ᵗ rz (zero-lᵀ rX)
    mono (suc n) = wk-rᵗ (⊑ᵀ→ᵗ (rR (suc n)) (B1ᵀ rX (R→⊑ᵀ (rR (suc n)))))
  Psi q H H₂ (gl f st) = gl (λ n → Psi q H H₂ (f n)) (λ n → ψ-congᵗ {q = q} (st n))
  Psi {φ = φ} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gi {j = j} {f = f} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gi (λ D → 𝓥 D × 𝓖₀ (pψ q D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W₀ (pψ q D)) (λ (x , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez g → Psi q {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pψ q D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
          (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pψ q D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
       (λ (x , c₀) → Wv c₀)
       (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (aboveV cx′ (λ t₁ rt → wrap (ψᵒ q t₁) (R-ψ q q rt))))
       (λ x o (_ , c₀) → x , cg x (pψ o) c₀)
       (λ h → ψ-congᵗ {q = q} (hm h)) (λ d → R-ψ q q (rf d))
  Psi q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pψ q D)) Bc (Psi q H H₂ g₀)
       (λ η e → Psi q {𝓖 = λ D → 𝓖 D × 𝓑 η (pψ q D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
       (R-ψ q q et) (λ η e η′ e′ d → R-ψ q q (eg η e η′ e′ d)) (λ η e → ψ-congᵗ {q = q} (m η e)) (λ η e η′ e′ u → ψ-congᵗ {q = q} (mm η e η′ e′ u))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Psi q H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-ψ q q r₁) (λ η e η′ e′ d → R-ψ q q (r₂ η e η′ e′ d)) (Psi q H H₂ go) (λ k → Psi q H H₂ (gO k)) (ψ-congᵗ {q = q} mo) (λ k → ψ-congᵗ {q = q} (mO k))
  Psi q H H₂ (gw {le = le} 𝓖₁ inc₁ g) =
    gw (λ E → 𝓥 E × 𝓖₁ (pψ q E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Psi q proj₂ proj₁ g)
  Psi {c = c} {t = t} {φ = φ₀ ⊔ fk zero} q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gclo {φ = φ₀} {t = t₀} {g = g} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) =
    gw (𝓖ₐ 𝓖ᵗ) (λ {C} c₁ → Ctx-wkC C (H₂ c₁) , subst (λ E → 𝓖ᵗ (pψ q E)) (sym (asr-asl C)) (inc₁ (H c₁)))
       (gclo (𝓖ₐ 𝓖ᵗ) (λ c₁ → c₁) (λ η → 𝓖ₐ (𝓖ᵍ η))
         (λ {η} {η′} {C} {C′} e x o (_ , c₁) → x , Bc e (Ctx-wkC C′ x) (pψ (wk≈ asr asr o)) c₁)
         (gw (𝓖₂ 𝓖ᵗ) (λ {D} (x , c₁) → Ctx-wkC D x , c₁) (Psi q proj₂ proj₁ gt))
         (λ η → gw (𝓖₂ (𝓖ᵍ η)) (λ {D} (x , c₁) → Ctx-wkC D x , c₁) (Psi q proj₂ proj₁ (gg η)))
         (rwk (R-ψ q q rt)) (λ η η′ d → rwk (R-ψ q q (rg η η′ d)))
         (λ η h → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (m η h)))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (mm η η′ h u))))
         (λ {D} (_ , c₁) → at≡ (run-wkC asr D (ψᵒ q t₀)) {Q = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dt c₁ G₁)))
         (λ η {D} (_ , c₁) → at≡ (run-wkC asr D (ψᵒ q (g η))) {Q = λ X → ∀ {K} (q₁ : InF K (Fl ⊔ φ₀)) → Dem X q₁} (λ G₁ q₁ → demFl q₁ (dg η c₁ G₁)))
         (λ {D} (_ , c₁) → at≡ (run-wkC asr D (ψᵒ q t₀)) {Q = λ X → ∀ {C′ : Cx t ((Fl ⊔ φ₀) ⊔ fk X)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → x , ch₀ c₁ G₁ (Ctx-wkC C′ x) (pψ (wk≈ asr asr o))))
         (λ η {D} (_ , c₁) → at≡ (run-wkC asr D (ψᵒ q (g η))) {Q = λ X → ∀ {C′ : Cx t ((Fl ⊔ φ₀) ⊔ fk X)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → x , chS η c₁ G₁ (Ctx-wkC C′ x) (pψ (wk≈ asr asr o)))))
    where
    𝓖ₐ : ∀ {η} → ClT c (φ₀ ⊔ fk η) → ClT t ((Fl ⊔ φ₀) ⊔ fk η)
    𝓖ₐ 𝓖′ D = 𝓥 D × 𝓖′ (pψ q (wkC asr D))
    𝓖₂ : ∀ {η} → ClT c (φ₀ ⊔ fk η) → ClT t (Fl ⊔ (φ₀ ⊔ fk η))
    𝓖₂ 𝓖′ E = 𝓥 E × 𝓖′ (pψ q E)
  Psi {t = t} q H H₂ (gΩ {m = m} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W₀ Wf hb Wv lΩ St cg hm rf) = PsiΩ q {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv lΩ St cg hm rf (cmp< m t)

  PsiΩ {c = c} {t = t} {φ = φ} {m = m} q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv lΩ St cg hm rf (pen s) =
    gΩ 𝓖₀′
       (λ ξ {C} {C′} c₁ x o → x , inc₀ ξ (H c₁) (Ctx-wkC C′ x) (pψ (≈ᶜ-wkˡ swp o)))
       (λ ξ D → W₀ ξ (pψ q (wkC swp D)))
       (λ ξ {D} (x , c₀) u ru →
          subst (λ v → runᶜ (W₀ ξ (pψ q (wkC swp D))) u ≅ˢ runᶜ D (owk swp (ψᵒ q (h ξ (intoU r v))))) (sym (out-intoU′ s u))
                (subst (λ v → runᶜ (W₀ ξ (pψ q (wkC swp D))) u ≅ˢ v) (run-wkC swp D (ψᵒ q (h ξ (intoU r u)))) (Wf ξ c₀ u ru)))
       (λ 𝓔′ inc″ ξ z rz g →
          subst (λ v → Gᵀ t (𝓔′ ξ) (owk swp (ψᵒ q (h ξ (intoU r v))))) (sym (out-intoU′ s z))
          (gw (𝓖₅ 𝓔′ ξ) (λ {D} c₁ → Ctx-wkC D (proj₁ (inc″ ξ c₁)) , (D , c₁ , refl))
              (Psi q proj₂ proj₁ (hb (𝓧₃ 𝓔′) (λ ξ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ c₁) }) ξ z rz
                 (intoG r (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outG s g)))))))
       (λ ξ (x , c₀) → Wv ξ c₀)
       (intoG s (outG r lΩ))
       (λ ξ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) → cx′ , St ξ c₀ (aboveΩ (Ctx-wkC C′ cx′) (λ t₁ rt →
          let Wp = wrap (owk swp (ψᵒ q t₁)) (rwk (R-ψ q q rt))
          in proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ (pψ q (wkC swp D))) (proj₁ Wp)) (sym (run-wkC swp C′ (ψᵒ q t₁))) (proj₂ (proj₂ (proj₂ Wp))))))
       (λ ξ ξ′ {C} {C′} x o (_ , c₀) → x , cg ξ ξ′ (Ctx-wkC C x) (pψ (wk≈ swp swp o)) c₀)
       (λ {ξ} {ξ′} {z} {z′} u → subst₂ (λ v v′ → owk swp (ψᵒ q (h ξ (intoU r v))) ⊑ᵗ owk swp (ψᵒ q (h ξ′ (intoU r v′)))) (sym (out-intoU′ s z)) (sym (out-intoU′ s z′))
          (wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (hm u)))))
       (λ ξ ξ′ d z z′ l → subst₂ (λ v v′ → Rᵒ t (owk swp (ψᵒ q (h ξ (intoU r v)))) (owk swp (ψᵒ q (h ξ′ (intoU r v′))))) (sym (out-intoU′ s z)) (sym (out-intoU′ s z′))
          (rwk (R-ψ q q (rf ξ ξ′ d z z′ l))))
    where
    𝓖₀′ : ∀ ξ → ClT t (ξ ⊔ (Fl ⊔ φ))
    𝓖₀′ ξ D = 𝓥 D × 𝓖₀ ξ (pψ q (wkC swp D))
    𝓧₃ : (∀ ξ → ClT t (ξ ⊔ (Fl ⊔ φ))) → ∀ ξ → ClT c (ξ ⊔ φ)
    𝓧₃ 𝓔′ ξ E = Σ _ λ D → 𝓔′ ξ D × (E ≡ pψ q (wkC swp D))
    𝓖₅ : (∀ ξ → ClT t (ξ ⊔ (Fl ⊔ φ))) → ∀ ξ → ClT t (Fl ⊔ (ξ ⊔ φ))
    𝓖₅ 𝓔′ ξ E = 𝓥 E × 𝓧₃ 𝓔′ ξ (pψ q E)
  PsiΩ {c = c} {t = t} {φ = φ} {m = m} q {𝓖 = 𝓖} {𝓧 = 𝓧} {fe = fe} {r = r} {h = h} H H₂ 𝓖₀ inc₀ W₀ Wf hb Wv lΩ St cg hm rf chain =
    gl (λ n → gw 𝓖₇ (λ {C} c₁ → Ctx-wkC {le = dupr2 {a = Fl} {b = φ}} C (H₂ c₁) , inc₀ ξ* (H c₁) (Ctx-wkC {le = dupr2 {a = Fl} {b = φ}} C (H₂ c₁)) (pψ (≈ᶜ-wkˡ (dupr2 {a = Fl} {b = φ}) (ctxᶜ-refl C (H₂ c₁)))))
                 (Psi q {𝓖 = 𝓖₇} {𝓧 = 𝓖₀ ξ*} proj₂ proj₁ (hb 𝓖₀ (λ ξ c₁ → c₁) ξ* (zt n) (G→R (zG n)) (intoG r (zG n)))))
       (λ n → wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = q} (hm (zm n)))))
    where
    ξ* = Fl ⊔ φ
    f : O m ξ* → O m ξ*
    f z = owk dupr2 (ψᵒ r (h ξ* (intoU r z)))
    zt : ℕ → O m ξ*
    zt = chainᵒ proj₁ f
    𝓖₆ : ClT m (Fl ⊔ (ξ* ⊔ φ))
    𝓖₆ E = 𝓥 E × 𝓖₀ ξ* (pψ r E)
    𝓖₇ : ClT t (Fl ⊔ (ξ* ⊔ φ))
    𝓖₇ E = 𝓥 E × 𝓖₀ ξ* (pψ q E)
    zG : ∀ n → Gᵀ m (W₀ ξ* ⟪ 𝓖₀ ξ* ⟫ᵀ) (zt n)
    zG zero = gw 𝓥 (λ {D} (x , _) → Ctx-wkC D x) (outG r lΩ)
    zG (suc n) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Ctx-wkC D x , St ξ* c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             owk dupr2 (ψᵒ r t₁) , rwk (R-ψ r r rt) , (λ h₁ → wk-rᵀ (P0ᵀ {q = r} rt h₁)) ,
             subst (λ v → v ≅ˢ runᶜ (W₀ ξ* C) (owk dupr2 (ψᵒ r t₁))) (sym (run-wkC dupr2 D (ψᵒ r t₁))) (runᶜ-≅ o (rwk (R-ψ r r rt))))))
         (Psi r {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ ξ*} proj₂ proj₁ (hb 𝓖₀ (λ ξ c₁ → c₁) ξ* (zt n) (G→R (zG n)) (intoG r (zG n))))
    zm : ∀ n → zt n ⊑ᵗ zt (suc n)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ m)) (P0ᵀ {q = r} (rf ξ* ξ* (∼ᶠ-refl ξ*) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ m)))))
    zm (suc n) = wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = r} (hm (zm n))))
```
