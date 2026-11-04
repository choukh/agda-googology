# 高度抽象: `Gq` 沿层号搬运

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFTr](LadderNFTr.lagda.md) 生成, 下面的说明是原文件的. 与 `OCF.Free.Tr` 同形, 多 `gcl`, `gΩ↓`, `gm`. `gm` 行的 $z$ 同样搬运: 这是 `ι↓` 读穿搬运的地方, `shD` 在 `ptr` 上逐层下移. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfTr (𝕊 : HtS) where

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
open import OCF.Free.Eq using (⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᴵ→⊑ᴵ)
open RestrQ

Hq-tr : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {y : Q m a φ χ} {D : Cx m b φ χ} → Hq g y (ptr e D) → Hq g (trQ e y) D
Hq-tr g₀ e h = tt
Hq-tr g₁ e h = tt
Hq-tr g₂ e h G = ⊑ᴵ-≅ˡ e (h G)

Hq-tr⁻ : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {y : Q m b φ χ} {D : Cx m a φ χ} → Hq g y (ptr⁻ e D) → Hq g (tr⁻Q e y) D
Hq-tr⁻ g₀ e h = tt
Hq-tr⁻ g₁ e h = tt
Hq-tr⁻ g₂ e h G = ⊑ᴵ-≅ˡ (≅ᴵ-sym e) (h G)

bkC : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) → Cx m j ξ ζ → Cx m (repQ (resQ {m} q e)) ξ ζ
bkC zero      (s≅ e) D = ptr⁻ e D
bkC (suc q)   (s≅ e) D = bkC q e D
bkC (lim n q) (l≅ f) D = bkC q (f n) D

bkC⁻ : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) → Cx m j ξ ζ → Cx m (repQ (res⁻Q {m} q e)) ξ ζ
bkC⁻ zero      (s≅ e) D = ptr e D
bkC⁻ (suc q)   (s≅ e) D = bkC⁻ q e D
bkC⁻ (lim n q) (l≅ f) D = bkC⁻ q (f n) D

rbC : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Cx m j ξ ζ) (u : Q m (repQ (resQ {m} q e)) ξ ζ) → runᶜ (bkC q e D) u ≡ runᶜ D (backQ (resQ q e) u)
rbC zero      (s≅ e) D u = refl
rbC (suc q)   (s≅ e) D u = rbC q e D u
rbC (lim n q) (l≅ f) D u = rbC q (f n) D u

rbC⁻ : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) (D : Cx m j ξ ζ) (u : Q m (repQ (res⁻Q {m} q e)) ξ ζ) → runᶜ (bkC⁻ q e D) u ≡ runᶜ D (backQ (res⁻Q q e) u)
rbC⁻ zero      (s≅ e) D u = refl
rbC⁻ (suc q)   (s≅ e) D u = rbC⁻ q e D u
rbC⁻ (lim n q) (l≅ f) D u = rbC⁻ q (f n) D u

cbC : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Cx m j ξ ζ) → Ctxᶜ D → Ctxᶜ (bkC q e D)
cbC zero      (s≅ e) D c = c
cbC (suc q)   (s≅ e) D c = cbC q e D c
cbC (lim n q) (l≅ f) D c = cbC q (f n) D c

cbC⁻ : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) (D : Cx m j ξ ζ) → Ctxᶜ D → Ctxᶜ (bkC⁻ q e D)
cbC⁻ zero      (s≅ e) D c = c
cbC⁻ (suc q)   (s≅ e) D c = cbC⁻ q e D c
cbC⁻ (lim n q) (l≅ f) D c = cbC⁻ q (f n) D c

obC : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {D : Cx m j ξ ζ} {D′ : Cx m j ξ′ ζ′} → D ≈ᶜ D′ → bkC q e D ≈ᶜ bkC q e D′
obC zero      (s≅ e) o = ptr⁻ o
obC (suc q)   (s≅ e) o = obC q e o
obC (lim n q) (l≅ f) o = obC q (f n) o

obC⁻ : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {D : Cx m j ξ ζ} {D′ : Cx m j ξ′ ζ′} → D ≈ᶜ D′ → bkC⁻ q e D ≈ᶜ bkC⁻ q e D′
obC⁻ zero      (s≅ e) o = ptr o
obC⁻ (suc q)   (s≅ e) o = obC⁻ q e o
obC⁻ (lim n q) (l≅ f) o = obC⁻ q (f n) o

bmᵗ : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Q m (repQ (resQ {m} q e)) ξ ζ} {u′ : Q m (repQ (resQ {m} q e)) ξ′ ζ′} → u ⊑ᵗ u′ → backQ (resQ q e) u ⊑ᵗ backQ (resQ q e) u′
bmᵗ zero      (s≅ e) h = tr⁻ᵗ-cong h
bmᵗ (suc q)   (s≅ e) h = bmᵗ q e h
bmᵗ (lim n q) (l≅ f) h = bmᵗ q (f n) h

bmᵗ⁻ : ∀ {m j a b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {u : Q m (repQ (res⁻Q {m} q e)) ξ ζ} {u′ : Q m (repQ (res⁻Q {m} q e)) ξ′ ζ′} → u ⊑ᵗ u′ → backQ (res⁻Q q e) u ⊑ᵗ backQ (res⁻Q q e) u′
bmᵗ⁻ zero      (s≅ e) h = trᵗ-cong h
bmᵗ⁻ (suc q)   (s≅ e) h = bmᵗ⁻ q e h
bmᵗ⁻ (lim n q) (l≅ f) h = bmᵗ⁻ q (f n) h

Kl-bk : ∀ g {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) {D : Cx m j ξ ζ} → KlT g j D → KlT g (repQ (resQ {m} q e)) (bkC q e D)
Kl-bk g zero      (s≅ e) v = Kl-ptr⁻ g e v
Kl-bk g (suc q)   (s≅ e) v = Kl-bk g q e v
Kl-bk g (lim n q) (l≅ f) v = Kl-bk g q (f n) v

Kl-bk⁻ : ∀ g {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) {D : Cx m j ξ ζ} → KlT g j D → KlT g (repQ (res⁻Q {m} q e)) (bkC⁻ q e D)
Kl-bk⁻ g zero      (s≅ e) v = Kl-ptr g e v
Kl-bk⁻ g (suc q)   (s≅ e) v = Kl-bk⁻ g q e v
Kl-bk⁻ g (lim n q) (l≅ f) v = Kl-bk⁻ g q (f n) v

Trᵀ  : ∀ {g m a b φ χ} (ε : a ≅ᴵ b) {𝓖 : ClT m b φ χ} {𝓧 : ClT m a φ χ} {x : Q m a φ χ} → (∀ {C} → 𝓖 C → 𝓧 (ptr ε C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gq g m a 𝓧 x → Gq g m b 𝓖 (trQ ε x)
Tr⁻ᵀ : ∀ {g m a b φ χ} (ε : a ≅ᴵ b) {𝓖 : ClT m a φ χ} {𝓧 : ClT m b φ χ} {x : Q m b φ χ} → (∀ {C} → 𝓖 C → 𝓧 (ptr⁻ ε C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gq g m b 𝓧 x → Gq g m a 𝓖 (tr⁻Q ε x)
Bkᵀ  : ∀ {g m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) {𝓕 : ClT m j ξ ζ} {𝓕′ : ClT m (repQ (resQ {m} q e)) ξ ζ} {u} → (∀ {D} → 𝓕 D → 𝓕′ (bkC q e D)) → (∀ {D} → 𝓕 D → 𝓥 D) → Gq g m _ 𝓕′ u → Gq g m j 𝓕 (backQ (resQ q e) u)
Bk⁻ᵀ : ∀ {g m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) {𝓕 : ClT m j ξ ζ} {𝓕′ : ClT m (repQ (res⁻Q {m} q e)) ξ ζ} {u} → (∀ {D} → 𝓕 D → 𝓕′ (bkC⁻ q e D)) → (∀ {D} → 𝓕 D → 𝓥 D) → Gq g m _ 𝓕′ u → Gq g m j 𝓕 (backQ (res⁻Q q e) u)

Bkᵀ zero      (s≅ e) M V k = Tr⁻ᵀ e M V k
Bkᵀ (suc q)   (s≅ e) M V k = Bkᵀ q e M V k
Bkᵀ (lim n q) (l≅ f) M V k = Bkᵀ q (f n) M V k

Bk⁻ᵀ zero      (s≅ e) M V k = Trᵀ e M V k
Bk⁻ᵀ (suc q)   (s≅ e) M V k = Bk⁻ᵀ q e M V k
Bk⁻ᵀ (lim n q) (l≅ f) M V k = Bk⁻ᵀ q (f n) M V k

Trᵀ ε H H₂ g0 = g0
Trᵀ {g} ε H H₂ (gs 𝓚 v k clk cgk ho hq) =
  gs (λ D → 𝓥 D × 𝓚 (ptr ε D)) (λ c → H₂ c , v (H c)) (Trᵀ ε proj₂ proj₁ k)
     (λ {O₁} {C″} (x , c₁) f nd → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (trQ ε t) (R-tr₂ ε ε rt) G)) (ndT _ _ nd))
     (λ x o (_ , c₁) → x , cgk x (ptr o) c₁)
     (λ (_ , c₁) G → ho c₁ G)
     (λ (_ , c₁) → Hq-tr g ε (hq c₁))
Trᵀ ε H H₂ (gl f st) = gl (λ n → Trᵀ ε H H₂ (f n)) (λ n → trᵗ-cong {e = ε} {e′ = ε} (st n))
Trᵀ ε {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → 𝓥 D × 𝓖₀ (ptr ε D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (ptr ε D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez gz → Trᵀ ε {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr ε D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr ε D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) gz)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) nd → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (trQ ε t) (R-tr₂ ε ε rt))) (ndT _ _ nd))
     (λ x o (_ , c₀) → x , cg x (ptr o) c₀)
     (λ h → trᵗ-cong {e = ε} {e′ = ε} (hm h)) (λ d → R-tr₂ ε ε (rf d))
Trᵀ ε {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (ptr ε D)) Bc (Trᵀ ε H H₂ g₀′)
     (λ η e → Trᵀ ε {𝓖 = λ D → 𝓖 D × 𝓑 η (ptr ε D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-tr₂ ε ε et) (λ η e η′ e′ d → R-tr₂ ε ε (eg η e η′ e′ d)) (λ η e → trᵗ-cong {e = ε} {e′ = ε} (m₁ η e)) (λ η e η′ e′ u → trᵗ-cong {e = ε} {e′ = ε} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Trᵀ ε H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-tr₂ ε ε r₁) (λ η e η′ e′ d → R-tr₂ ε ε (r₂ η e η′ e′ d)) (Trᵀ ε H H₂ go) (λ k → Trᵀ ε H H₂ (gO k)) (trᵗ-cong {e = ε} {e′ = ε} mo) (λ k → trᵗ-cong {e = ε} {e′ = ε} (mO k))
Trᵀ ε H H₂ (gw {le = le} {lc = lc} 𝓖₁ inc₁ k) =
  gw (λ E → 𝓥 E × 𝓖₁ (ptr ε E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Trᵀ ε proj₂ proj₁ k)
Trᵀ ε {𝓖 = 𝓖} H H₂ (gclo 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gclo (λ D → 𝓥 D × 𝓖ᵗ (ptr ε D)) (λ c → H₂ c , inc₁ (H c)) (λ x o (_ , c₁) → x , cgᵗ x (ptr o) c₁)
     (λ η D → 𝓥 D × 𝓖ᵍ η (ptr ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr o) c₁)
     (Trᵀ ε proj₂ proj₁ gt) (λ η → Trᵀ ε proj₂ proj₁ (gg η))
     (R-tr₂ ε ε rt) (λ η η′ e → R-tr₂ ε ε (rg η η′ e))
     (λ η h → trᵗ-cong {e = ε} {e′ = ε} (m₁ η h)) (λ η η′ h u → trᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr o))
Trᵀ ε {𝓖 = 𝓖} H H₂ (gcl 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gcl (λ D → 𝓥 D × 𝓖ᵗ (ptr ε D)) (λ c → H₂ c , inc₁ (H c))
     (λ η D → 𝓥 D × 𝓖ᵍ η (ptr ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr o) c₁)
     (Trᵀ ε proj₂ proj₁ gt) (λ η → Trᵀ ε proj₂ proj₁ (gg η))
     (R-tr₂ ε ε rt) (λ η η′ e → R-tr₂ ε ε (rg η η′ e))
     (λ η h → trᵗ-cong {e = ε} {e′ = ε} (m₁ η h)) (λ η η′ h u → trᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr o))
Trᵀ {m = m} {b = b} {φ = φ} {χ = χ} ε {𝓖 = 𝓖} H H₂ (gΩ↓ {n = n} {k = k} {q = q₁} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ↓ (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (ptr ε D))
     (λ ξ ζ c x o → x , inc₀ ξ ζ (H c) x (ptr o))
     (λ ξ ζ D → W ξ ζ (ptr ε D))
     (λ ξ ζ (x , c₀) u ru → Wf ξ ζ c₀ u ru)
     (λ 𝓔′ inc″ ξ ζ z rz gz →
        Trᵀ ε {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ ζ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ ζ₁ c) }) ξ ζ z rz
               (intoGV q₁ (Gmono (λ { (x , E , (D , c , refl) , o) → x , D , c , o }) (outGV q₁ gz)))))
     (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
     (λ ξ ζ (x , c₀) (aboveΩ cx′ wrap) nd → cx′ , St ξ ζ c₀ (aboveΩ cx′ (λ t rt → wrap (trQ ε t) (R-tr₂ ε ε rt))) (ndT _ _ nd))
     (λ ξ ξ′ ζ ζ′ x o (_ , c₀) → x , cg ξ ξ′ ζ ζ′ x (ptr o) c₀)
     (λ u → trᵗ-cong {e = ε} {e′ = ε} (hm u))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → R-tr₂ ε ε (rf ξ ξ′ ζ ζ′ e dc z z′ l))
  where
  𝓧₃ : (∀ ξ ζ → ClT m b (ξ ⊔ φ) (lo n ζ ∪ χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo n ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ ptr ε D)
Trᵀ {g} {m = m} {a = a} {b = b} {φ = φ} {χ = χ} ε {𝓖 = 𝓖} H H₂ (gΩ {k = j} {r = q} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (ptr ε D))
     (λ ξ ζ c₁ x o → x , inc₀ ξ ζ (H c₁) x (ptr o))
     (λ ξ ζ D → bkC q ε (W ξ ζ (ptr ε D)))
     (λ ξ ζ {D} (x , c₀) u ru →
        subst (λ v → runᶜ (bkC q ε (W ξ ζ (ptr ε D))) u ≅ˢ runᶜ D (trQ ε (h ξ ζ (intoU (<→◃ q) (backQ (resQ q ε) v))))) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) u))
          (subst (λ y → y ≅ˢ runᶜ D (trQ ε (h ξ ζ (intoU (<→◃ q) (backQ (resQ q ε) u))))) (sym (rbC q ε (W ξ ζ (ptr ε D)) u))
             (Wf ξ ζ c₀ (backQ (resQ q ε) u) (R-back q ε ru))))
     (λ 𝓔′ inc″ ξ ζ z rz gz → subst (λ v → Gq g m b (𝓔′ ξ ζ) (trQ ε (h ξ ζ (intoU (<→◃ q) (backQ (resQ q ε) v))))) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) z))
        (Trᵀ ε {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c₁ → D , c₁ , refl) (λ c₁ → proj₁ (inc″ ξ ζ c₁))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ (backQ (resQ q ε) z) (R-back q ε rz)
               (intoG (<→◃ q) (Bkᵀ q ε {𝓕 = W ξ ζ ⟪ 𝓧₃ 𝓔′ ξ ζ ⟫ᵀ} {𝓕′ = (λ D → bkC q ε (W ξ ζ (ptr ε D))) ⟪ 𝓔′ ξ ζ ⟫ᵀ}
                  (λ { (x , E , (D , c₁ , refl) , o) → cbC q ε _ x , D , c₁ , obC q ε o }) proj₁ (outG (<→◃ (ltQ (resQ q ε))) gz))))))
     (λ ξ ζ (x , c₀) → Kl-bk g q ε (Wv ξ ζ c₀))
     (λ ξ ζ {D} {C″} (x , c₀) (aboveΩ cx′ wrap) nd → cx′ , St ξ ζ c₀ (aboveΩ cx′ (λ t rt →
         let Wp = wrap (trQ ε t) (R-tr₂ ε ε rt)
         in backQ (resQ q ε) (proj₁ Wp) , R-back q ε (proj₁ (proj₂ Wp)) , Fl-back q ε (proj₁ (proj₂ (proj₂ Wp))) ,
            subst (λ y → runᶜ C″ (trQ ε t) ≅ˢ y) (rbC q ε (W ξ ζ (ptr ε D)) (proj₁ Wp)) (proj₂ (proj₂ (proj₂ Wp))))) (ndT _ _ nd))
     (λ ξ ξ′ ζ ζ′ x o (_ , c₀) → x , cg ξ ξ′ ζ ζ′ x (ptr o) c₀)
     (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → trQ ε (h ξ ζ (intoU (<→◃ q) (backQ (resQ q ε) v))) ⊑ᵗ trQ ε (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q ε) v′)))) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) z)) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) z′)) (trᵗ-cong {e = ε} {e′ = ε} (hm (bmᵗ q ε u))))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → subst₂ (λ v v′ → Rq m b b (trQ ε (h ξ ζ (intoU (<→◃ q) (backQ (resQ q ε) v)))) (trQ ε (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q ε) v′))))) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) z)) (sym (out-intoU (<→◃ (ltQ (resQ q ε))) z′)) (R-tr₂ ε ε (rf ξ ξ′ ζ ζ′ e dc _ _ (R-back q ε l))))
  where
  𝓧₃ : (∀ ξ ζ → ClT m b (ξ ⊔ φ) (lo m ζ ∪ χ)) → ∀ ξ ζ → ClT m a (ξ ⊔ φ) (lo m ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ ptr ε D)
Trᵀ {g = g₀} (s≅ e) H H₂ (gm {r = zero} zc rz₁ gx) = gm {r = zero} tt₁ (R-tr₂ e e rz₁) (Trᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Trᵀ {g = g₁} (s≅ e) H H₂ (gm {r = zero} zc rz₁ gx) = gm {r = zero} tt₁ (R-tr₂ e e rz₁) (Trᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Trᵀ {g = g₂} (s≅ e) {𝓧 = 𝓧} H H₂ (gm {r = zero} zc rz₁ gx) =
  gm {r = zero} (λ 𝓔 i → Trᵀ e {𝓖 = Dq zero 𝓔} {𝓧 = Dq zero (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr (s≅ e) D))}
                   (λ { (x , C , c , d , o) → x , ptr (s≅ e) C , (C , c , refl) , d , ptr o }) proj₁
                   (zc (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr (s≅ e) D)) (λ { (D , c , refl) → H (i c) })))
     (R-tr₂ e e rz₁) (Trᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Trᵀ {g = g₀} (l≅ f) H H₂ (gm {r = self n} zc rz₁ gx) = gm {r = self n} tt₁ (R-tr₂ (f n) (f n) rz₁) (Trᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)
Trᵀ {g = g₁} (l≅ f) H H₂ (gm {r = self n} zc rz₁ gx) = gm {r = self n} tt₁ (R-tr₂ (f n) (f n) rz₁) (Trᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)
Trᵀ {g = g₂} (l≅ f) {𝓧 = 𝓧} H H₂ (gm {r = self n} zc rz₁ gx) =
  gm {r = self n} (λ 𝓔 i → Trᵀ (f n) {𝓖 = Dq (self n) 𝓔} {𝓧 = Dq (self n) (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr (l≅ f) D))}
                   (λ { (x , C , c , d , o) → x , ptr (l≅ f) C , (C , c , refl) , d , ptr o }) proj₁
                   (zc (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr (l≅ f) D)) (λ { (D , c , refl) → H (i c) })))
     (R-tr₂ (f n) (f n) rz₁) (Trᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)

Tr⁻ᵀ ε H H₂ g0 = g0
Tr⁻ᵀ {g} ε H H₂ (gs 𝓚 v k clk cgk ho hq) =
  gs (λ D → 𝓥 D × 𝓚 (ptr⁻ ε D)) (λ c → H₂ c , v (H c)) (Tr⁻ᵀ ε proj₂ proj₁ k)
     (λ {O₁} {C″} (x , c₁) f nd → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (tr⁻Q ε t) (R-tr⁻₂ ε ε rt) G)) (ndT⁻ _ _ nd))
     (λ x o (_ , c₁) → x , cgk x (ptr⁻ o) c₁)
     (λ (_ , c₁) G → ho c₁ G)
     (λ (_ , c₁) → Hq-tr⁻ g ε (hq c₁))
Tr⁻ᵀ ε H H₂ (gl f st) = gl (λ n → Tr⁻ᵀ ε H H₂ (f n)) (λ n → tr⁻ᵗ-cong {e = ε} {e′ = ε} (st n))
Tr⁻ᵀ ε {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → 𝓥 D × 𝓖₀ (ptr⁻ ε D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (ptr⁻ ε D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez gz → Tr⁻ᵀ ε {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr⁻ ε D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr⁻ ε D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) gz)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) nd → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (tr⁻Q ε t) (R-tr⁻₂ ε ε rt))) (ndT⁻ _ _ nd))
     (λ x o (_ , c₀) → x , cg x (ptr⁻ o) c₀)
     (λ h → tr⁻ᵗ-cong {e = ε} {e′ = ε} (hm h)) (λ d → R-tr⁻₂ ε ε (rf d))
Tr⁻ᵀ ε {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (ptr⁻ ε D)) Bc (Tr⁻ᵀ ε H H₂ g₀′)
     (λ η e → Tr⁻ᵀ ε {𝓖 = λ D → 𝓖 D × 𝓑 η (ptr⁻ ε D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-tr⁻₂ ε ε et) (λ η e η′ e′ d → R-tr⁻₂ ε ε (eg η e η′ e′ d)) (λ η e → tr⁻ᵗ-cong {e = ε} {e′ = ε} (m₁ η e)) (λ η e η′ e′ u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Tr⁻ᵀ ε H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-tr⁻₂ ε ε r₁) (λ η e η′ e′ d → R-tr⁻₂ ε ε (r₂ η e η′ e′ d)) (Tr⁻ᵀ ε H H₂ go) (λ k → Tr⁻ᵀ ε H H₂ (gO k)) (tr⁻ᵗ-cong {e = ε} {e′ = ε} mo) (λ k → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mO k))
Tr⁻ᵀ ε H H₂ (gw {le = le} {lc = lc} 𝓖₁ inc₁ k) =
  gw (λ E → 𝓥 E × 𝓖₁ (ptr⁻ ε E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Tr⁻ᵀ ε proj₂ proj₁ k)
Tr⁻ᵀ ε {𝓖 = 𝓖} H H₂ (gclo 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gclo (λ D → 𝓥 D × 𝓖ᵗ (ptr⁻ ε D)) (λ c → H₂ c , inc₁ (H c)) (λ x o (_ , c₁) → x , cgᵗ x (ptr⁻ o) c₁)
     (λ η D → 𝓥 D × 𝓖ᵍ η (ptr⁻ ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr⁻ o) c₁)
     (Tr⁻ᵀ ε proj₂ proj₁ gt) (λ η → Tr⁻ᵀ ε proj₂ proj₁ (gg η))
     (R-tr⁻₂ ε ε rt) (λ η η′ e → R-tr⁻₂ ε ε (rg η η′ e))
     (λ η h → tr⁻ᵗ-cong {e = ε} {e′ = ε} (m₁ η h)) (λ η η′ h u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr⁻ o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr⁻ o))
Tr⁻ᵀ ε {𝓖 = 𝓖} H H₂ (gcl 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) =
  gcl (λ D → 𝓥 D × 𝓖ᵗ (ptr⁻ ε D)) (λ c → H₂ c , inc₁ (H c))
     (λ η D → 𝓥 D × 𝓖ᵍ η (ptr⁻ ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr⁻ o) c₁)
     (Tr⁻ᵀ ε proj₂ proj₁ gt) (λ η → Tr⁻ᵀ ε proj₂ proj₁ (gg η))
     (R-tr⁻₂ ε ε rt) (λ η η′ e → R-tr⁻₂ ε ε (rg η η′ e))
     (λ η h → tr⁻ᵗ-cong {e = ε} {e′ = ε} (m₁ η h)) (λ η η′ h u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr⁻ o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr⁻ o))
Tr⁻ᵀ {m = m} {a = b} {φ = φ} {χ = χ} ε {𝓖 = 𝓖} H H₂ (gΩ↓ {n = n} {k = k} {q = q₁} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ↓ (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (ptr⁻ ε D))
     (λ ξ ζ c x o → x , inc₀ ξ ζ (H c) x (ptr⁻ o))
     (λ ξ ζ D → W ξ ζ (ptr⁻ ε D))
     (λ ξ ζ (x , c₀) u ru → Wf ξ ζ c₀ u ru)
     (λ 𝓔′ inc″ ξ ζ z rz gz →
        Tr⁻ᵀ ε {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ ζ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ ζ₁ c) }) ξ ζ z rz
               (intoGV q₁ (Gmono (λ { (x , E , (D , c , refl) , o) → x , D , c , o }) (outGV q₁ gz)))))
     (λ ξ ζ (x , c₀) → Wv ξ ζ c₀)
     (λ ξ ζ (x , c₀) (aboveΩ cx′ wrap) nd → cx′ , St ξ ζ c₀ (aboveΩ cx′ (λ t rt → wrap (tr⁻Q ε t) (R-tr⁻₂ ε ε rt))) (ndT⁻ _ _ nd))
     (λ ξ ξ′ ζ ζ′ x o (_ , c₀) → x , cg ξ ξ′ ζ ζ′ x (ptr⁻ o) c₀)
     (λ u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (hm u))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → R-tr⁻₂ ε ε (rf ξ ξ′ ζ ζ′ e dc z z′ l))
  where
  𝓧₃ : (∀ ξ ζ → ClT m b (ξ ⊔ φ) (lo n ζ ∪ χ)) → ∀ ξ ζ → ClT m _ (ξ ⊔ φ) (lo n ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ ptr⁻ ε D)
Tr⁻ᵀ {g} {m = m} {a = b} {b = a} {φ = φ} {χ = χ} ε {𝓖 = 𝓖} H H₂ (gΩ {k = j} {r = q} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ (λ ξ ζ D → 𝓥 D × 𝓖₀ ξ ζ (ptr⁻ ε D))
     (λ ξ ζ c₁ x o → x , inc₀ ξ ζ (H c₁) x (ptr⁻ o))
     (λ ξ ζ D → bkC⁻ q ε (W ξ ζ (ptr⁻ ε D)))
     (λ ξ ζ {D} (x , c₀) u ru →
        subst (λ v → runᶜ (bkC⁻ q ε (W ξ ζ (ptr⁻ ε D))) u ≅ˢ runᶜ D (tr⁻Q ε (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q ε) v))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) u))
          (subst (λ y → y ≅ˢ runᶜ D (tr⁻Q ε (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q ε) u))))) (sym (rbC⁻ q ε (W ξ ζ (ptr⁻ ε D)) u))
             (Wf ξ ζ c₀ (backQ (res⁻Q q ε) u) (R-back⁻ q ε ru))))
     (λ 𝓔′ inc″ ξ ζ z rz gz → subst (λ v → Gq g m b (𝓔′ ξ ζ) (tr⁻Q ε (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q ε) v))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) z))
        (Tr⁻ᵀ ε {𝓖 = 𝓔′ ξ ζ} {𝓧 = 𝓧₃ 𝓔′ ξ ζ} (λ {D} c₁ → D , c₁ , refl) (λ c₁ → proj₁ (inc″ ξ ζ c₁))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ ζ₁ {E} → λ { (D , c₁ , refl) → proj₂ (inc″ ξ₁ ζ₁ c₁) }) ξ ζ (backQ (res⁻Q q ε) z) (R-back⁻ q ε rz)
               (intoG (<→◃ q) (Bk⁻ᵀ q ε {𝓕 = W ξ ζ ⟪ 𝓧₃ 𝓔′ ξ ζ ⟫ᵀ} {𝓕′ = (λ D → bkC⁻ q ε (W ξ ζ (ptr⁻ ε D))) ⟪ 𝓔′ ξ ζ ⟫ᵀ}
                  (λ { (x , E , (D , c₁ , refl) , o) → cbC⁻ q ε _ x , D , c₁ , obC⁻ q ε o }) proj₁ (outG (<→◃ (ltQ (res⁻Q q ε))) gz))))))
     (λ ξ ζ (x , c₀) → Kl-bk⁻ g q ε (Wv ξ ζ c₀))
     (λ ξ ζ {D} {C″} (x , c₀) (aboveΩ cx′ wrap) nd → cx′ , St ξ ζ c₀ (aboveΩ cx′ (λ t rt →
         let Wp = wrap (tr⁻Q ε t) (R-tr⁻₂ ε ε rt)
         in backQ (res⁻Q q ε) (proj₁ Wp) , R-back⁻ q ε (proj₁ (proj₂ Wp)) , Fl-back⁻ q ε (proj₁ (proj₂ (proj₂ Wp))) ,
            subst (λ y → runᶜ C″ (tr⁻Q ε t) ≅ˢ y) (rbC⁻ q ε (W ξ ζ (ptr⁻ ε D)) (proj₁ Wp)) (proj₂ (proj₂ (proj₂ Wp))))) (ndT⁻ _ _ nd))
     (λ ξ ξ′ ζ ζ′ x o (_ , c₀) → x , cg ξ ξ′ ζ ζ′ x (ptr⁻ o) c₀)
     (λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ v v′ → tr⁻Q ε (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q ε) v))) ⊑ᵗ tr⁻Q ε (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q ε) v′)))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) z)) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) z′)) (tr⁻ᵗ-cong {e = ε} {e′ = ε} (hm (bmᵗ⁻ q ε u))))
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → subst₂ (λ v v′ → Rq m b b (tr⁻Q ε (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q ε) v)))) (tr⁻Q ε (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q ε) v′))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) z)) (sym (out-intoU (<→◃ (ltQ (res⁻Q q ε))) z′)) (R-tr⁻₂ ε ε (rf ξ ξ′ ζ ζ′ e dc _ _ (R-back⁻ q ε l))))
  where
  𝓧₃ : (∀ ξ ζ → ClT m b (ξ ⊔ φ) (lo m ζ ∪ χ)) → ∀ ξ ζ → ClT m a (ξ ⊔ φ) (lo m ζ ∪ χ)
  𝓧₃ 𝓔′ ξ ζ E = Σ _ λ D → 𝓔′ ξ ζ D × (E ≡ ptr⁻ ε D)
Tr⁻ᵀ {g = g₀} (s≅ e) H H₂ (gm {r = zero} zc rz₁ gx) = gm {r = zero} tt₁ (R-tr⁻₂ e e rz₁) (Tr⁻ᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Tr⁻ᵀ {g = g₁} (s≅ e) H H₂ (gm {r = zero} zc rz₁ gx) = gm {r = zero} tt₁ (R-tr⁻₂ e e rz₁) (Tr⁻ᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Tr⁻ᵀ {g = g₂} (s≅ e) {𝓧 = 𝓧} H H₂ (gm {r = zero} zc rz₁ gx) =
  gm {r = zero} (λ 𝓔 i → Tr⁻ᵀ e {𝓖 = Dq zero 𝓔} {𝓧 = Dq zero (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr⁻ (s≅ e) D))}
                   (λ { (x , C , c , d , o) → x , ptr⁻ (s≅ e) C , (C , c , refl) , d , ptr⁻ o }) proj₁
                   (zc (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr⁻ (s≅ e) D)) (λ { (D , c , refl) → H (i c) })))
     (R-tr⁻₂ e e rz₁) (Tr⁻ᵀ (s≅ e) (λ (c , n) → H c , n) (λ (c , n) → H₂ c) gx)
Tr⁻ᵀ {g = g₀} (l≅ f) H H₂ (gm {r = self n} zc rz₁ gx) = gm {r = self n} tt₁ (R-tr⁻₂ (f n) (f n) rz₁) (Tr⁻ᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)
Tr⁻ᵀ {g = g₁} (l≅ f) H H₂ (gm {r = self n} zc rz₁ gx) = gm {r = self n} tt₁ (R-tr⁻₂ (f n) (f n) rz₁) (Tr⁻ᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)
Tr⁻ᵀ {g = g₂} (l≅ f) {𝓧 = 𝓧} H H₂ (gm {r = self n} zc rz₁ gx) =
  gm {r = self n} (λ 𝓔 i → Tr⁻ᵀ (f n) {𝓖 = Dq (self n) 𝓔} {𝓧 = Dq (self n) (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr⁻ (l≅ f) D))}
                   (λ { (x , C , c , d , o) → x , ptr⁻ (l≅ f) C , (C , c , refl) , d , ptr⁻ o }) proj₁
                   (zc (λ E → Σ _ λ D → 𝓔 D × (E ≡ ptr⁻ (l≅ f) D)) (λ { (D , c , refl) → H (i c) })))
     (R-tr⁻₂ (f n) (f n) rz₁) (Tr⁻ᵀ (l≅ f) (λ (c , n₁) → H c , n₁) (λ (c , n₁) → H₂ c) gx)
```
