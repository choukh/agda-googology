# 无记号主线 (十五): 加法的闭包

> **`AddT.Add`.**
> 脚本从 [UniformNF5Add](../Align/UniformNF5Add.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Add where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Free.Eq using (≅ᶻ-sym; _≅ˢ_; z≅; ≅ˢ-trans; toZ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Force using (Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Base
open import OCF.Free.Rules
open import OCF.Free.Strict
open import OCF.Free.Class
open import OCF.Free.ClassF using (inp-map)
open import OCF.Free.Good 
```

```agda
open RestrO
asr-asl : ∀ {c a b d} (C : Cx c (a ⊔ (b ⊔ d))) → wkC asr (wkC asl C) ≡ C
asr-asl C = trans (wkC-comp asr asl C) (wkC-id C)

pr-wk : ∀ {c a φ ψ} (le : ∀ {L} → Ev L ψ → Ev L φ) (C : Cx c (a ⊔ ψ)) → wkC proj₁ (wkC (λ e → proj₁ e , le (proj₂ e)) C) ≡ wkC proj₁ C
pr-wk le C = wkC-comp proj₁ (λ e → proj₁ e , le (proj₂ e)) C

module AddT {c α} {𝓐 : ClT c α} {W : O c α} (gW : Gᵀ c 𝓐 W) (wW : WFl W)
            (cgA : ∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓐 C′ → 𝓐 C)
            (clA : ∀ {O₁ C″} → 𝓐 O₁ → FlOverᵀ W O₁ C″ → 𝓐 C″)
            (cxA : ∀ {C} → 𝓐 C → Ctxᶜ C)
            (hoA : ∀ {C} → 𝓐 C → HonT W C) where
  rW = WFl.rW wW

  𝓐𝓧 : ∀ {φ} → ClT c φ → ClT c (α ⊔ φ)
  𝓐𝓧 𝓧 E = 𝓐 (wkC proj₁ E) × 𝓧 (pa W E)

  rW⊕ : ∀ {φ ψ} {t : O c φ} {t′ : O c ψ} → Rᵒ c c t t′ → Rᵒ c c (W ⊕ t) (W ⊕ t′)
  rW⊕ {t = t} r = R-⊕ (∼ᶠ-refl α) rW r

  flW : ∀ {φ ψ} {t : O c ψ} {D : Cx c (α ⊔ φ)} {E : Cx c (α ⊔ ψ)} → D ≈ᶜ E → Rᵒ c c t t → (G : Goodᴺ (toZ (runᶜ E (W ⊕ t)))) →
        Σ (Goodᴺ (toZ (runᶜ (wkC proj₁ D) W))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
  flW {D = D} o rt G = proj₁ J , ⊑-trans (proj₂ J) (proj₂ L)
    where
    L = B1ᵀ {x = owk proj₁ W} {W = W} rt (wk-lᵀ (R→⊑ᵀ rW)) o G
    J = pull≡ (run-wkC proj₁ D W) (proj₁ L)

  Add : ∀ {φ} {𝓐₁ : ClT c (α ⊔ φ)} {𝓧 : ClT c φ} {y : O c φ} → (∀ {C} → 𝓐₁ C → 𝓐 (wkC proj₁ C)) → (∀ {C} → 𝓐₁ C → 𝓧 (pa W C)) → Gᵀ c 𝓧 y → Gᵀ c 𝓐₁ (W ⊕ y)
  Add inc H g0 = gw 𝓐 inc gW
  Add {φ = φ} {𝓐₁ = 𝓐₁} inc H (gs {a = b} 𝓚 v g clk cgk ho) =
    gs (𝓐𝓧 𝓚) (λ c → inc c , v (H c)) (Add proj₁ proj₂ g)
       (λ {O₁} {C″} (c , c₁) f′ →
         clA c (flo-overᵀ (Ctx-wkC C″ (cxoᵀ f′)) (λ t rt G →
           let J = pull≡ (sym (run-wkC proj₁ C″ t)) G
               L = flwᵀ f′ (owk proj₁ t) (rwk rt) (proj₁ J)
               N = flW (ctxᶜ-refl O₁ (Ctx-unwk O₁ (cxA c))) (G→R g) (proj₁ L)
           in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (proj₂ L) (proj₂ J)))) ,
         clk c₁ (flo-overᵀ (wW , cxoᵀ f′) (λ t rt G → flwᵀ f′ (W ⊕ t) (rW⊕ rt) G)))
       (λ {C} {C′} x o (c , c₁) → cgA (Ctx-wkC C x) (wk≈ proj₁ proj₁ o) c , cgk (wW , x) (pa rW o) c₁)
       (λ {D} (c , c₁) G → λ { (inl k) → let N = flW (ctxᶜ-refl D (Ctx-unwk D (cxA c))) (G→R g) G in demUp k (toLevel-⊑ (forceᴺ-HS _ (proj₁ N)) (forceᴺ-HS _ G) (proj₂ N)) (hoA c (proj₁ N) k)
                               ; (inr k) → ho c₁ G k })
  Add inc H (gl f st) = gl (λ n → Add inc H (f n)) (λ n → ⊕-congᵗ rW (st n))
  Add {φ = φ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gi {j = j} {f = f} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gi (𝓐𝓧 𝓖₀) (λ c → inc c , inc₀ (H c)) (λ D → W₀ (pa W D)) (λ (c , c₀) u eu → Wf c₀ u eu)
       (λ 𝓔′ inc″ z ez g → Add {𝓐₁ = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pa W D)} (λ c → proj₁ (inc″ c)) (λ {D} c → D , c , refl)
          (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pa W D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
              (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
       (λ (c , c₀) → Wv c₀)
       (λ {D} {C′} (c , c₀) (aboveV cx′ wrap) →
         clA c (flo-overᵀ (Ctx-wkC C′ cx′) (λ t rt G →
           let J  = pull≡ (sym (run-wkC proj₁ C′ t)) G
               Wp = wrap (owk proj₁ t) (rwk rt)
               u  = proj₁ Wp
               eu = proj₁ (proj₂ Wp)
               d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf c₀ u eu)
               dz = toZ-≅ d
               H₂ = Goodᴺ-tr dz (proj₁ J)
               N  = flW (ctxᶜ-refl D (Ctx-unwk D (cxA c))) (rf eu) H₂
           in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dz) H₂ (proj₁ J))) (proj₂ J)))) ,
         St c₀ (aboveV (wW , cx′) (λ t rt → wrap (W ⊕ t) (rW⊕ rt))))
       (λ {C} {C′} x o (c , c₀) → cgA (Ctx-wkC C x) (wk≈ proj₁ proj₁ o) c , cg (wW , x) (pa rW o) c₀)
       (λ h → ⊕-congᵗ rW (hm h)) (λ d → rW⊕ (rf d))
  Add {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
    gŝ (λ η D → 𝓑 η (pa W D)) Bc (Add inc H g₀)
       (λ η e → Add {𝓐₁ = λ D → 𝓐₁ D × 𝓑 η (pa W D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → inc c) (λ (c , b) → H c , b) (gg η e))
       (rW⊕ et) (λ η e η′ e′ d → rW⊕ (eg η e η′ e′ d)) (λ η e → ⊕-congᵗ rW (m η e)) (λ η e η′ e′ h → ⊕-congᵗ rW (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Add inc H (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    gĉ ys hy dy G₀ l₀ Gg lE ez ezg (rW⊕ r₁) (λ η e η′ e′ d → rW⊕ (r₂ η e η′ e′ d)) (Add inc H go) (λ k → Add inc H (gO k)) (⊕-congᵗ rW mo) (λ k → ⊕-congᵗ rW (mO k))
  Add {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gw {le = le} {x = x} 𝓖₁ inc₁ g) =
    gw (𝓐𝓧 𝓖₁) (λ {C} c → subst 𝓐 (sym (pr-wk le C)) (inc c) , inc₁ (H c)) (Add proj₁ proj₂ g)
  Add {φ = φ₀ ⊔ fk zero} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gclo {φ = φ₀} {t = t} {g = g} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) =
    gw (𝓖ₐ 𝓖ᵗ) (λ {C} c → cast (inc c) (inc₁ (H c)))
       (gclo (𝓖ₐ 𝓖ᵗ) (λ c → c) (λ η → 𝓖ₐ (𝓖ᵍ η))
         (λ {η} {η′} {C} {C′} e x o (c , c₁) → cgA (Ctx-wkC (wkC asr C′) (Ctx-wkC C′ x)) (wk≈ proj₁ proj₁ (wk≈ asr asr o)) c , Bc e (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr asr o)) c₁)
         (gw (𝓐𝓧 𝓖ᵗ) (λ c → c) (Add proj₁ proj₂ gt))
         (λ η → gw (𝓐𝓧 (𝓖ᵍ η)) (λ c → c) (Add proj₁ proj₂ (gg η)))
         (rwk (rW⊕ rt)) (λ η η′ d → rwk (rW⊕ (rg η η′ d)))
         (λ η h → wk-lᵗ (wk-rᵗ (⊕-congᵗ rW (m η h)))) (λ η η′ h u → wk-lᵗ (wk-rᵗ (⊕-congᵗ rW (mm η η′ h u))))
         (λ {D} (c , c₁) → at≡ (run-wkC asr D (W ⊕ t)) {Q = λ X → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem X q} (dt⊔ {D = D} c (G→R gt) (dt c₁)))
         (λ η {D} (c , c₁) → at≡ (run-wkC asr D (W ⊕ g η)) {Q = λ X → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem X q} (dt⊔ {D = D} c (rg η η (≅ᴵ-refl η)) (dg η c₁)))
         (λ {D} (ca , c₁) → at≡ (run-wkC asr D (W ⊕ t)) {Q = λ X → ∀ {C′ : Cx c ((α ⊔ φ₀) ⊔ fk X)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → cgA (Ctx-wkC (wkC asr C′) (Ctx-wkC C′ x)) (wk≈ proj₁ proj₁ (wk≈ asr asr o)) ca , ch₀ c₁ G₁ (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr asr o))))
         (λ η {D} (ca , c₁) → at≡ (run-wkC asr D (W ⊕ g η)) {Q = λ X → ∀ {C′ : Cx c ((α ⊔ φ₀) ⊔ fk X)} → Ctxᶜ C′ → C′ ≈ᶜ D → 𝓖ₐ (𝓖ᵍ X) C′}
             (λ G₁ {C′} x o → cgA (Ctx-wkC (wkC asr C′) (Ctx-wkC C′ x)) (wk≈ proj₁ proj₁ (wk≈ asr asr o)) ca , chS η c₁ G₁ (wW , Ctx-wkC C′ x) (pa rW (wk≈ asr asr o)))))
    where
    𝓖ₐ : ∀ {η} → ClT c (φ₀ ⊔ fk η) → ClT c ((α ⊔ φ₀) ⊔ fk η)
    𝓖ₐ 𝓖′ D = 𝓐 (wkC proj₁ (wkC asr D)) × 𝓖′ (pa W (wkC asr D))
    cast : ∀ {C : Cx c (α ⊔ (φ₀ ⊔ fk zero))} → 𝓐 (wkC proj₁ C) → 𝓖ᵗ (pa W C) → 𝓖ₐ 𝓖ᵗ (wkC asl C)
    cast {C} c c₁ = subst (λ E → 𝓐 (wkC proj₁ E) × 𝓖ᵗ (pa W E)) (sym (asr-asl C)) (c , c₁)
    dt⊔ : ∀ {η} {D : Cx c ((α ⊔ φ₀) ⊔ fk η)} {y : O c (φ₀ ⊔ fk η)} → 𝓐 (wkC proj₁ (wkC asr D)) → Rᵒ c c y y →
          ((G₁ : Goodᴺ (toZ (runᶜ (wkC asr D) (W ⊕ y)))) → ∀ {K} (q : InF K φ₀) → Dem (lvG G₁) q) →
          (G₁ : Goodᴺ (toZ (runᶜ (wkC asr D) (W ⊕ y)))) → ∀ {K} (q : InF K (α ⊔ φ₀)) → Dem (lvG G₁) q
    dt⊔ {D = D} c ry ho G₁ (inl k) = demUp k (toLevel-⊑ (forceᴺ-HS _ (proj₁ N)) (forceᴺ-HS _ G₁) (proj₂ N)) (hoA c (proj₁ N) k)
      where N = flW (ctxᶜ-refl (wkC asr D) (Ctx-unwk (wkC asr D) (cxA c))) ry G₁
    dt⊔ c ry ho G₁ (inr k) = ho G₁ k
  Add {φ = φ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (gΩ {m = m} {fe = fe} {r = r} {h = h₀} 𝓖₀ inc₀ W₀ Wf hb Wv St cg hm rf) =
    gΩ 𝓖₀′
       (λ ξ {C} {C′} c x o → cgA (Ctx-wkC (wkC swp C′) (Ctx-wkC C′ x)) (≈ᶜ-wkˡ proj₁ (≈ᶜ-wkʳ proj₁ (≈ᶜ-wkˡ swp o))) (inc c) ,
                              inc₀ ξ (H c) (wW , Ctx-wkC C′ x) (pa rW (≈ᶜ-wkˡ swp o)))
       (λ ξ D → W₀ ξ (pa W (wkC swp D)))
       (λ ξ {D} (c , c₀) u ru → subst (λ v → runᶜ (W₀ ξ (pa W (wkC swp D))) u ≅ˢ v) (run-wkC swp D (W ⊕ h₀ ξ (intoU (<→◃ r) u))) (Wf ξ c₀ u ru))
       (λ 𝓔′ inc″ ξ z rz g →
          gw (𝓐𝓧 (𝓧₃ 𝓔′ ξ)) (λ {D} c → proj₁ (inc″ ξ c) , (D , c , refl))
             (Add proj₁ proj₂ (hb (𝓧₃ 𝓔′) (λ ξ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ c) }) ξ z rz
                (intoG (<→◃ r) (Gmono (λ { (x , E , (D , c , refl) , o) → x , D , c , o }) (outG (<→◃ r) g))))))
       (λ ξ (c , c₀) → Wv ξ c₀)
       (λ ξ {D} {C′} (c , c₀) (aboveΩ cx′ wrap) →
          clA c (flo-overᵀ (Ctx-wkC (wkC swp C′) (Ctx-wkC C′ cx′)) (λ t rt G →
            let J₁ = pull≡ (sym (run-wkC proj₁ (wkC swp C′) t)) G
                J₂ = pull≡ (sym (run-wkC swp C′ (owk proj₁ t))) (proj₁ J₁)
                Wp = wrap (owk swp (owk proj₁ t)) (rwk (rwk rt))
                u  = proj₁ Wp
                ru = proj₁ (proj₂ Wp)
                d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ Wp))) (Wf ξ c₀ u ru)
                dz = toZ-≅ d
                H₂ = Goodᴺ-tr dz (proj₁ J₂)
                N  = flW (ctxᶜ-refl (wkC swp D) (Ctx-unwk (wkC swp D) (cxA c))) (rf ξ ξ (∼ᶠ-refl ξ) u u ru) H₂
            in proj₁ N , ⊑-trans (proj₂ N) (⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dz) H₂ (proj₁ J₂))) (⊑-trans (proj₂ J₂) (proj₂ J₁))))) ,
          St ξ c₀ (aboveΩ (wW , Ctx-wkC C′ cx′) (λ t rt →
            let Wp = wrap (owk swp (W ⊕ t)) (rwk (rW⊕ rt)) in
            proj₁ Wp , proj₁ (proj₂ Wp) , proj₁ (proj₂ (proj₂ Wp)) ,
            subst (λ v → v ≅ˢ runᶜ (W₀ ξ (pa W (wkC swp D))) (proj₁ Wp)) (sym (run-wkC swp C′ (W ⊕ t))) (proj₂ (proj₂ (proj₂ Wp))))))
       (λ ξ ξ′ {C} {C′} x o (c , c₀) → cgA (Ctx-wkC (wkC swp C) (Ctx-wkC C x)) (wk≈ proj₁ proj₁ (wk≈ swp swp o)) c , cg ξ ξ′ (wW , Ctx-wkC C x) (pa rW (wk≈ swp swp o)) c₀)
       (λ h → wk-lᵗ (wk-rᵗ (⊕-congᵗ rW (hm h))))
       (λ ξ ξ′ d z z′ l → rwk (rW⊕ (rf ξ ξ′ d z z′ l)))
    where
    𝓖₀′ : ∀ ξ → ClT c (ξ ⊔ (α ⊔ φ))
    𝓖₀′ ξ D = 𝓐 (wkC proj₁ (wkC swp D)) × 𝓖₀ ξ (pa W (wkC swp D))
    𝓧₃ : (∀ ξ → ClT c (ξ ⊔ (α ⊔ φ))) → ∀ ξ → ClT c (ξ ⊔ φ)
    𝓧₃ 𝓔′ ξ E = Σ _ λ D → 𝓔′ ξ D × (E ≡ pa W (wkC swp D))
```
