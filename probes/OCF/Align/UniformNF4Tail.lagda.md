# 数据树上的无符号闭包定理 (十): 嵌入与尾巴

> 接 [UniformNF4Good](UniformNF4Good.lagda.md). 结论先说:
>
> 1. **`Iota q : Gᵀ c 𝓧 x → Gᵀ d 𝓖 (ι q x)`.** 与 `Psi` 同形, 但没有后继行的内容.
> 2. **`TL : Good true 𝓧 y → Gᵀ c 𝓖 (tl (flo k) (cvFlo k) y)`, 只要 $C\in\mathcal G$ 推出 `tlo C` ∈ $\mathcal X$.** 值层的好树进入树层. 地板 `flo k` 的 `Dem` 由 `Hon` 给 (`demFlo`). 第 0 层的闭包行取 `Ch0` 的链.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Tail where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (_≅ˢ_; z≅; s≅; l≅; ŝ≅; ĉ≅; upˡ; upʳ; toZ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; tf)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.Uniform4Base
open import OCF.Align.UniformNF4Base
open import OCF.Align.UniformNF4Rules
open import OCF.Align.UniformNF4Strict
open import OCF.Align.UniformNF4Class
open import OCF.Align.UniformNF4ClassF
open import OCF.Align.UniformNF4Good
```

## §1 嵌入

```agda
Iota : ∀ {c d φ} (q : c <ᴸ d) {𝓖 : ClT d φ} {𝓧 : ClT c φ} {x : O c φ} → (∀ {C} → 𝓖 C → 𝓧 (pι q C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gᵀ c 𝓧 x → Gᵀ d 𝓖 (ι q x)
Iota q H H₂ g0 = g0
Iota q H H₂ (gs 𝓚 v g clk cgk ho) =
  gs (λ D → 𝓥 D × 𝓚 (pι q D)) (λ c → H₂ c , v (H c)) (Iota q proj₂ proj₁ g)
     (λ {O₁} {C″} (x , c₁) f → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (ι q t) (R-ι q rt) G)))
     (λ x o (_ , c₁) → x , cgk x (pι o) c₁)
     (λ (_ , c₁) G k → ho c₁ G k)
Iota q H H₂ (gl f st) = gl (λ n → Iota q H H₂ (f n)) (λ n → ι-congᵗ {q = q} (st n))
Iota q {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → 𝓥 D × 𝓖₀ (pι q D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (pι q D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → Iota q {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ pι q D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ pι q D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (ι q t) (R-ι q rt))))
     (λ x o (_ , c₀) → x , cg x (pι o) c₀)
     (λ h → ι-congᵗ {q = q} (hm h)) (λ d → R-ι q (rf d))
Iota q {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (pι q D)) Bc (Iota q H H₂ g₀)
     (λ η e → Iota q {𝓖 = λ D → 𝓖 D × 𝓑 η (pι q D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-ι q et) (λ η e η′ e′ d → R-ι q (eg η e η′ e′ d)) (λ η e → ι-congᵗ {q = q} (m η e)) (λ η e η′ e′ u → ι-congᵗ {q = q} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Iota q H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-ι q r₁) (λ η e η′ e′ d → R-ι q (r₂ η e η′ e′ d)) (Iota q H H₂ go) (λ k → Iota q H H₂ (gO k)) (ι-congᵗ {q = q} mo) (λ k → ι-congᵗ {q = q} (mO k))
Iota q H H₂ (gw {le = le} 𝓖₁ inc₁ g) =
  gw (λ E → 𝓥 E × 𝓖₁ (pι q E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Iota q proj₂ proj₁ g)
Iota {d = d} {φ = φ₀ ⊔ fk zero} q {𝓖 = 𝓖} H H₂ (gclo {φ = φ₀} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) =
  gclo (λ D → 𝓥 D × 𝓖ᵗ (pι q D)) (λ c → H₂ c , inc₁ (H c)) (λ η D → 𝓥 D × 𝓖ᵍ η (pι q D))
     (λ e x o (_ , c₁) → x , Bc e x (pι o) c₁)
     (Iota q proj₂ proj₁ gt) (λ η → Iota q proj₂ proj₁ (gg η))
     (R-ι q rt) (λ η η′ e → R-ι q (rg η η′ e))
     (λ η h → ι-congᵗ {q = q} (m η h)) (λ η η′ h u → ι-congᵗ {q = q} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (pι o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (pι o))
Iota {c = c} {d = d} {φ = φ} q {𝓖 = 𝓖} H H₂ (gΩ {m = m} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv lΩ St cg hm rf) =
  gΩ (λ ξ D → 𝓥 D × 𝓖₀ ξ (pι q D))
     (λ ξ c x o → x , inc₀ ξ (H c) x (pι o))
     (λ ξ D → W ξ (pι q D))
     (λ ξ {D} (x , c₀) u ru → subst (λ v → runᶜ (W ξ (pι q D)) u ≅ˢ runᶜ D (ι q (h ξ (intoU r v)))) (sym (out-intoU′ (tr< r q) u)) (Wf ξ c₀ u ru))
     (λ 𝓔′ inc″ ξ z rz g → subst (λ v → Gᵀ d (𝓔′ ξ) (ι q (h ξ (intoU r v)))) (sym (out-intoU′ (tr< r q) z))
        (Iota q {𝓖 = 𝓔′ ξ} {𝓧 = 𝓧₃ 𝓔′ ξ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ c) }) ξ z rz
               (intoG r (Gmono (λ { (x , E , (D , c , refl) , o) → x , D , c , o }) (outG (tr< r q) g))))))
     (λ ξ (x , c₀) → Wv ξ c₀)
     (intoG (tr< r q) (outG r lΩ))
     (λ ξ (x , c₀) (aboveΩ cx′ wrap) → cx′ , St ξ c₀ (aboveΩ cx′ (λ t rt → wrap (ι q t) (R-ι q rt))))
     (λ ξ ξ′ x o (_ , c₀) → x , cg ξ ξ′ x (pι o) c₀)
     (λ {ξ} {ξ′} {z} {z′} u → subst₂ (λ v v′ → ι q (h ξ (intoU r v)) ⊑ᵗ ι q (h ξ′ (intoU r v′))) (sym (out-intoU′ (tr< r q) z)) (sym (out-intoU′ (tr< r q) z′)) (ι-congᵗ {q = q} (hm u)))
     (λ ξ ξ′ e z z′ l → subst₂ (λ v v′ → Rᵒ d (ι q (h ξ (intoU r v))) (ι q (h ξ′ (intoU r v′)))) (sym (out-intoU′ (tr< r q) z)) (sym (out-intoU′ (tr< r q) z′)) (R-ι q (rf ξ ξ′ e z z′ l)))
  where
  𝓧₃ : (∀ ξ → ClT d (ξ ⊔ φ)) → ∀ ξ → ClT c (ξ ⊔ φ)
  𝓧₃ 𝓔′ ξ E = Σ _ λ D → 𝓔′ ξ D × (E ≡ pι q D)
```

## §2 尾巴

```agda
Hl : ∀ {c} k → ClT c (flo k) → Cl k → Set
Hl zero      𝓖 𝓧 = 𝓧 idO
Hl (suc k)   𝓖 𝓧 = ∀ {C} → 𝓖 C → 𝓧 (tlo C)
Hl (lim f s) 𝓖 𝓧 = ∀ {C} → 𝓖 C → 𝓧 (tlo C)

demFlo : ∀ {k K X} (q : InF K (flo k)) → k ⊑ᴵ X → Dem X q
demFlo {k = suc k₀} ink (s⊑ e r) = inj₁ (via e r)
demFlo {k = lim f s} inb u = u

Dn₁ : ∀ {c k₀ k} (r : k ◃₁ k₀) → Cl k₀ → ClT c (flo k)
Dn₁ {c} {k₀} r 𝓧 E = Ctxᶜ E × (Σ (Cx c (flo k₀)) λ C → 𝓧 (tlo C) × (E ≈ᶜ C))

hdn₁ : ∀ {c k₀ k} (r : k ◃₁ k₀) {𝓧 : Cl k₀} → Hl {c} k (Dn₁ r 𝓧) (Dn r 𝓧)
hdn₁ {k = zero}    r = refl
hdn₁ {k = suc _}   r (x , C , c , o) = x , tlo C , c , tlo o
hdn₁ {k = lim _ _} r (x , C , c , o) = x , tlo C , c , tlo o

leUp : ∀ {k k₀} (r : k ◃₁ k₀) {L} → Ev L (flo k₀) → Ev L (flo k)
leUp {k} {k₀} r v = toFlo k (λ q → cvFlo k₀ v (τ₁ r q))

TL : ∀ {c k} {𝓖 : ClT c (flo k)} {𝓧 : Cl k} {y : Ordˢ k} → Hl k 𝓖 𝓧 → (∀ {C} → 𝓖 C → 𝓥 C) → Good true 𝓧 y → y ≅ˢ y → Gᵀ c 𝓖 (tl (flo k) (cvFlo k) y)
TL H H₂ bz ey = g0
TL {k = zero} H H₂ (b1 z≅) ey = gs 𝓥 H₂ g0 (λ _ f → cxoᵀ f) (λ x o _ → x) (λ c G → λ { () })
TL {k = zero} H H₂ (bs 𝓚 v eb g clk cgk ho) ey =
  gs 𝓥 H₂ (TL {𝓖 = 𝓥} {𝓧 = 𝓚} (v H) (λ c → c) g eb) (λ _ f → cxoᵀ f) (λ x o _ → x) (λ c G → λ { () })
TL {c = c} {k = suc k₀} {𝓖 = 𝓖} H H₂ (bs {a = a} 𝓚 v eb g clk cgk ho) ey =
  gs (λ C → 𝓥 C × 𝓚 (tlo C)) (λ c₁ → H₂ c₁ , v (H c₁)) (TL {𝓖 = λ C → 𝓥 C × 𝓚 (tlo C)} {𝓧 = 𝓚} proj₂ proj₁ g eb)
     (λ (x , c₁) f → cxoᵀ f , clk tt c₁ (flo-over (cxoᵀ f) (λ t et G → flwᵀ f (tl (flo (suc k₀)) (cvFlo (suc k₀)) t) (R-tl et) G)))
     (λ x o (_ , c₁) → x , cgk tt x (tlo o) c₁)
     (λ (_ , c₁) G q → demFlo q (ho c₁ G))
TL {c = c} {k = lim f₀ s₀} {𝓖 = 𝓖} H H₂ (bs {a = a} 𝓚 v eb g clk cgk ho) ey =
  gs (λ C → 𝓥 C × 𝓚 (tlo C)) (λ c₁ → H₂ c₁ , v (H c₁)) (TL {𝓖 = λ C → 𝓥 C × 𝓚 (tlo C)} {𝓧 = 𝓚} proj₂ proj₁ g eb)
     (λ (x , c₁) f → cxoᵀ f , clk tt c₁ (flo-over (cxoᵀ f) (λ t et G → flwᵀ f (tl (flo (lim f₀ s₀)) (cvFlo (lim f₀ s₀)) t) (R-tl et) G)))
     (λ x o (_ , c₁) → x , cgk tt x (tlo o) c₁)
     (λ (_ , c₁) G q → demFlo q (ho c₁ G))
TL H H₂ (bl h st) ey = gl (λ n → TL H H₂ (h n) (l-invˢ ey n)) (λ n → tl-congᵒ (st n))
TL {k = zero} H H₂ (bi {p = ()} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey
TL {c = c} {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey =
  gi (λ C → 𝓥 C × 𝓖₀ (tlo C)) (λ c₁ → H₂ c₁ , inc₀ (H c₁)) (λ C → W (tlo C)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → TL {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)} (λ {C} c₁ → C , c₁ , refl) (λ c₁ → proj₁ (inc″ c₁))
        (hb (λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)) (λ { (C , c₁ , refl) → proj₂ (inc″ c₁) }) z ez
            (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , E , (C , c₁ , refl) , o) → x , C , c₁ , o })) g)))
        (i-respˢ ey ez))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (above cx′ (λ t et → wrap (tl (flo (suc k₀)) (cvFlo (suc k₀)) t) (R-tl et))))
     (λ x o (_ , c₀) → x , cg x (tlo o) c₀)
     (λ h → tl-congᵒ (hm h)) (λ d → R-tl (i-respˢ ey d))
TL {c = c} {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey =
  gi (λ C → 𝓥 C × 𝓖₀ (tlo C)) (λ c₁ → H₂ c₁ , inc₀ (H c₁)) (λ C → W (tlo C)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → TL {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)} (λ {C} c₁ → C , c₁ , refl) (λ c₁ → proj₁ (inc″ c₁))
        (hb (λ E → Σ _ λ C → 𝓔′ C × (E ≡ tlo C)) (λ { (C , c₁ , refl) → proj₂ (inc″ c₁) }) z ez
            (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , E , (C , c₁ , refl) , o) → x , C , c₁ , o })) g)))
        (i-respˢ ey ez))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (above cx′ (λ t et → wrap (tl (flo (lim f₀ s₀)) (cvFlo (lim f₀ s₀)) t) (R-tl et))))
     (λ x o (_ , c₀) → x , cg x (tlo o) c₀)
     (λ h → tl-congᵒ (hm h)) (λ d → R-tl (i-respˢ ey d))
TL {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bu {r = zero} g) ey =
  gw (Dn₁ zero 𝓧) (λ {C} c₁ → Ctx-wkC C (H₂ c₁) , C , H c₁ , ≈ᶜ-wkˡ (leUp zero) (ctxᶜ-refl C (H₂ c₁)))
     (TL {𝓖 = Dn₁ zero 𝓧} {𝓧 = Dn zero 𝓧} (hdn₁ zero) proj₁ g (u-reflˢ zero ey))
TL {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bu {r = self n} g) ey =
  gw (Dn₁ (self n) 𝓧) (λ {C} c₁ → Ctx-wkC C (H₂ c₁) , C , H c₁ , ≈ᶜ-wkˡ (leUp (self n)) (ctxᶜ-refl C (H₂ c₁)))
     (TL {𝓖 = Dn₁ (self n) 𝓧} {𝓧 = Dn (self n) 𝓧} (hdn₁ (self n)) proj₁ g (u-reflˢ (self n) ey))
TL {k = zero} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) ey =
  gĉ C.ys C.hy C.dy C.G₀ (≅-refl⁰ _) C.Gk (λ k → ≅-refl⁰ _)
     (toZ-≅ et) (λ η e η′ e′ d → toZ-≅ (eg η e η′ e′ d)) (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d))
     (TL H H₂ g₀ et)
     (λ n → TL {𝓖 = 𝓖} {𝓧 = 𝓧 ∧ 𝓑 (toLevel (C.ys n) (C.hy n))} (H , bp (C.P n)) H₂ (gg _ (C.dy n) (H , bp (C.P n))) (eg _ _ _ _ (≅ᴵ-refl _)))
     (tl-congᵒ (m _ _)) (λ n → tl-congᵒ (mm _ _ _ _ (C.lmono n)))
  where module C = Ch0 𝓑 H g₀ gg m mm d₀ dE ch₀ chS
TL {k = suc k₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) ey =
  gŝ (λ η C → 𝓑 η (tlo C)) Bc (TL {𝓖 = 𝓖} {𝓧 = 𝓧} (λ {C} c₁ → H c₁) H₂ g₀ et)
     (λ η e → TL {𝓖 = λ C → 𝓖 C × 𝓑 η (tlo C)} {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c₁ , b) → H c₁ , b) (λ c₁ → H₂ (proj₁ c₁)) (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
     (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d)) (λ η e → tl-congᵒ (m η e)) (λ η e η′ e′ u → tl-congᵒ (mm η e η′ e′ u))
     (λ c₁ G → d₀ (H c₁) G) (λ η e c₁ b G → dE η e (H c₁) b G) (λ c₁ G → ch₀ (H c₁) G) (λ η e c₁ b G → chS η e (H c₁) b G)
TL {k = lim f₀ s₀} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (bŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) ey =
  gŝ (λ η C → 𝓑 η (tlo C)) Bc (TL {𝓖 = 𝓖} {𝓧 = 𝓧} (λ {C} c₁ → H c₁) H₂ g₀ et)
     (λ η e → TL {𝓖 = λ C → 𝓖 C × 𝓑 η (tlo C)} {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c₁ , b) → H c₁ , b) (λ c₁ → H₂ (proj₁ c₁)) (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
     (R-tl et) (λ η e η′ e′ d → R-tl (eg η e η′ e′ d)) (λ η e → tl-congᵒ (m η e)) (λ η e η′ e′ u → tl-congᵒ (mm η e η′ e′ u))
     (λ c₁ G → d₀ (H c₁) G) (λ η e c₁ b G → dE η e (H c₁) b G) (λ c₁ G → ch₀ (H c₁) G) (λ η e c₁ b G → chS η e (H c₁) b G)
TL H H₂ (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) (ĉ≅ ec dt dg eo eO) =
  gĉ ys hy dy G₀ l₀ Gg lE dt dg (R-tl eo) (λ η e η′ e′ d → R-tl (eO η e η′ e′ d))
     (TL H H₂ go eo) (λ k → TL H H₂ (gO k) (eO _ _ _ _ (≅ᴵ-refl _))) (tl-congᵒ mo) (λ k → tl-congᵒ (mO k))
```
