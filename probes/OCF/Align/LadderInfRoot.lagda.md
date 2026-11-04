# 高度抽象: 根层 $\dot\Omega$

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFRoot](LadderNFRoot.lagda.md) 生成, 下面的说明是原文件的. `Ω̇G₀`: 最底的 $\dot\Omega$ (`Q h₀ zero`) 在任何等级都是 `Gq`. 与 `OCF.Free.Omega` 同形, 守卫 `Brᵀ` 就是那里的守卫. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfRoot (𝕊 : HtS) where

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

open import OCF.Align.LadderInfTail 𝕊
open import OCF.Align.LadderInfRead 𝕊
open import OCF.Free.Aux using (one⁰)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; Ωˢ-≅; Ωˢ-refl)
open import OCF.Free.Floor using (⊔∼; fk∼)
-- (同上)
open RestrQ

Cz : Flr → Set
Cz φ = Cx h₀ zero φ (κ Fl)

CzT : Flr → Set₁
CzT φ = ClT h₀ zero φ (κ Fl)
```

## §1 根地板非紧的 $\Omega_\eta$

```agda
lr : ∀ {φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) {L} → Ev L φ → Ev L (flo η)
lr η cv v = toFlo η (cv v)

R-root : ∀ {η η′ φ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L (flo η′) → Simᴵ η′ L} → η ≅ᴵ η′ → NZ η → Rq h₀ zero zero (tl {χ = χ} φ cv (Ωˢ η)) (tl {χ = ρ} (flo η′) cv′ (Ωˢ η′))
R-root (s≅ e) nz = ri e (λ x y d → rwk (R-tl d))
R-root (l≅ h) nz = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

rootmono : ∀ {a b φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ a L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ b L} → NZ a → NZ b → a ⊑ᴵ b → tl {c = zero} {χ = κ Fl} φ cv (Ωˢ a) ⊑ᵗ tl {c = zero} {χ = κ Fl} φ′ cv′ (Ωˢ b)
rootmono {a = a} {b = b} {cv = cv} {cv′ = cv′} na nb u {C} {C′} o G G′ =
  ⊑-trans (≅→⊑ (forceᴺ-≅ dA G GA)) (⊑-trans (tl-congᵒ (Ω-monoᵒ u) (wk≈ (lr a cv) sub-id (lr b cv′) sub-id o) GA GB) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dB) GB G′)))
  where
  dA = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr a cv) sub-id (≈ᶜ-reflˡ o)) (R-root {cv′ = cvFlo a} (≅ᴵ-refl a) na))
  dB = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr b cv′) sub-id (≈ᶜ-reflʳ o)) (R-root {cv′ = cvFlo b} (≅ᴵ-refl b) nb))
  GA = Goodᴺ-tr dA G
  GB = Goodᴺ-tr dB G′

VisΩ : ∀ {φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) → Cz φ → Set
VisΩ zero      cv C = ⊤
VisΩ (suc j)   cv C = Vis (suc j) (tlo (wkC (λ v → toFlo j (λ q → cv v (suc q))) sub-id C))
VisΩ (lim f s) cv C = ∀ n → Vis (f n) (tlo (wkC (λ v → toFlo (f n) (λ q → cv v (lim n q))) sub-id C))

hlV : ∀ k → Hl {κ Fl} k (λ E → 𝓥 E × Vis k (tlo E)) (Vis k)
hlV zero = vis tt (λ { (via _ ()) })
hlV (suc k) = proj₂
hlV (lim f s) = proj₂

hlI : ∀ {φ j} (le : ∀ {L} → Ev L φ → Ev L (flo j)) (𝓔 : CzT φ) → Hl {κ Fl} j (λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le sub-id C))) (Inp j ((λ C → tlo (wkC le sub-id C)) ⟪ 𝓔 ⟫))
hlI {j = zero} le 𝓔 = refl
hlI {j = suc j} le 𝓔 (x , C , c , o) = x , C , c , tlo o
hlI {j = lim f s} le 𝓔 (x , C , c , o) = x , C , c , tlo o

rootΩ : ∀ {g φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) {𝓖 : CzT φ} → (∀ {C} → 𝓖 C → Ctxᶜ C × VisΩ η cv C) → (∀ {K} (q : InF K φ) {X} → η ≅ᴵ zero → Dem X q) → Gq g h₀ zero 𝓖 (tl φ cv (Ωˢ η))
rootΩ {φ = φ} zero cv H hz₀ = gs 𝓥 (λ c → proj₁ (H c)) g0 (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ _ _ → (λ q → hz₀ q z≅) , (λ i q₀ → ⊥-elim (no< q₀))) (λ c → Hq-zero _)
rootΩ {φ = φ} (suc j) cv {𝓖 = 𝓖} H hz₀ =
  gi (λ C → Ctxᶜ C × VisΩ (suc j) cv C) H (λ C → tlo (wkC le sub-id C))
     (λ {C} (x , v) u eu → subst (λ w → run (tlo (wkC le sub-id C)) u ≅ˢ w) (run-wkC le sub-id C (tl (flo j) (cvFlo j) u))
          (run-≅ (tlo (ctxᶜ-refl (wkC le sub-id C) (Ctx-wkC C x))) eu))
     (λ 𝓔 inc″ z ez g →
        gw (λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le sub-id C)))
           (λ {C} c₁ → Ctx-wkC C (proj₁ (inc″ c₁)) , C , c₁ , ctxᶜ-refl (wkC le sub-id C) (Ctx-wkC C (proj₁ (inc″ c₁))))
           (TL {𝓖 = λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le sub-id C))} {𝓧 = Inp j ((λ C → tlo (wkC le sub-id C)) ⟪ 𝓔 ⟫)} (hlI le 𝓔) proj₁ g ez))
     (λ (x , v) → v)
     (λ {C} {C′} (x , v) (aboveV cx′ wrap) _ → cx′ , vis (Ctx-wkC C′ cx′) (λ {b} h t et fl G →
        at≡ (sym (run-wkC le sub-id C′ (tl (flo j) (cvFlo j) t))) {P = λ X → suc b ⊑ᴵ X}
          (λ G₁ →
            let Wp = wrap (qwk le sub-id (tl (flo j) (cvFlo j) t)) (rwk (R-tl et))
                u = proj₁ Wp
                eu = proj₁ (proj₂ Wp)
                fu = proj₁ (proj₂ (proj₂ Wp))
                d = proj₂ (proj₂ (proj₂ Wp))
            in pull d (cp v h u eu (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) fu)) G₁) G))
     (λ {C} {C′} x o (_ , v) → x , Vis-≈ (Ctx-wkC C x) (tlo (wk≈ le sub-id le sub-id o)) v)
     (λ h → wk-lᵗ (wk-rᵗ (tl-congᵒ h)))
     (λ d → rwk (R-tl d))
  where
  le : ∀ {L} → Ev L φ → Ev L (flo j)
  le v = toFlo j (λ q → cv v (suc q))
rootΩ {φ = φ} (lim f s) cv {𝓖 = 𝓖} H hz₀ =
  gl (λ n → gw (λ E → 𝓥 E × Vis (f n) (tlo E))
              (λ {C} c₁ → Ctx-wkC C (proj₁ (H c₁)) , proj₂ (H c₁) n)
              (TL {𝓖 = λ E → 𝓥 E × Vis (f n) (tlo E)} {𝓧 = Vis (f n)} (hlV (f n)) proj₁ (Ωg (f n)) (Ωˢ-refl (f n))))
     (λ n → wk-lᵗ (wk-rᵗ (tl-congᵒ (Ω-monoᵒ (s n)))))
```

## §2 $\dot\Omega_0^{(0)}$: 闭包的守卫

```agda
FlT : ∀ {χ} → Ordᴵ → Q h₀ zero χ (κ Fl) → Set
FlT b t = ∀ {k₀ χ₁} {x : Ordˢ k₀} → x ≅ˢ x → x ⊑ᴱ Ωˢ b → tl {c = zero} {χ = χ₁} (flo k₀) (cvFlo k₀) x ⊑ᵀ t

CQ : ∀ {ψ} → Cz ψ → Ordᴵ → Set
CQ C b = ∀ {χ} {D : Cz χ} → D ≈ᶜ C → (t : Q h₀ zero χ (κ Fl)) → Rq h₀ zero zero t t → FlT b t → (G : Goodᴺ (toZ (runᶜ D t))) → suc b ⊑ᴵ lvG G

record Brᵀ {ψ} (η : Ordᴵ) (C : Cz ψ) : Set where
  constructor br-mk
  field
    cxB : Ctxᶜ C
    br  : ∀ {b} → b ≺ᴵ η → CQ C b
    η₋  : Ordᴵ
    φ₋  : Flr
    cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L
    D₋  : Cz φ₋
    o₋  : D₋ ≈ᶜ C
    G₋  : Goodᴺ (toZ (runᶜ D₋ (tl φ₋ cv₋ (Ωˢ η₋))))
    eη  : η ≅ᴵ lvG G₋
    nz₋ : NZ η₋
    h₋  : η₋ ≺ᴵ η
open Brᵀ

Ωvia : ∀ {a b} → a ≺ᴵ b → Ωˢ a ⊑ᴱ Ωˢ b
Ωvia (via e q) = Ωlt e q

≺ᴵ-up : ∀ {b A B} → b ≺ᴵ A → A ⊑ᴵ B → b ≺ᴵ B
≺ᴵ-up (via e q) h = ≺ᴵ-respˡ e (sim h q)

zlt : ∀ {b} → suc zero ⊑ᴵ b → zero <ᴵ b
zlt (s⊑ z≅ q) = q

trans< : ∀ {x a b} → x <ᴵ a → a <ᴵ b → x <ᴵ b
trans< x zero      = suc x
trans< x (suc q)   = suc (trans< x q)
trans< x (lim n q) = lim n (trans< x q)

τ : ∀ {a b} → a <ᴵ b → Simᴵ (suc a) b
τ q zero    = q
τ q (suc x) = trans< x q

one⊑ : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → suc zero ⊑ᴵ i
one⊑ z p nz with <ᴵ-dec z p
... | injᵃ r          = s⊑′ r
... | injᵇ (via e ())
... | injᶜ z≅         = ⊥-elim nz

NZ-≅₁ : ∀ {i j} → NZ i → i ≅ᴵ j → NZ j
NZ-≅₁ nz (s≅ _) = tt
NZ-≅₁ nz (l≅ _) = tt
NZ-≅₁ () z≅

ω1b : ∀ {b x L} → b ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
ω1b {b} e q z nb = ω1′ (⊑ᴵ-≅ʳ (one⊑ z q (NZ-≅₁ nb e)) (≅ᴵ-sym e))
  where
  ω1′ : suc zero ⊑ᴵ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
  ω1′ (s⊑ z≅ r) = Ω<ᴱ z≅ r

rd : ∀ {φ₀ χ η₀ b} {D₀ : Cz φ₀} {D : Cz χ} {cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ η₀ L} → NZ η₀ → D₀ ≈ᶜ D →
     (G₀ : Goodᴺ (toZ (runᶜ D₀ (tl φ₀ cv₀ (Ωˢ η₀))))) → b ≺ᴵ lvG G₀ → (t : Q h₀ zero χ (κ Fl)) → tl {c = zero} {χ = κ Fl} (flo η₀) (cvFlo η₀) (Ωˢ η₀) ⊑ᵀ t → (G : Goodᴺ (toZ (runᶜ D t))) → suc b ⊑ᴵ lvG G
rd {η₀ = η₀} {D₀ = D₀} {cv₀ = cv₀} nz o G₀ h t fl G =
  s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                         (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
  where
  L = fl (≈ᶜ-wkˡ (lr η₀ cv₀) sub-id o) G
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr η₀ cv₀) sub-id (≈ᶜ-reflˡ o)) (R-root {cv = cv₀} {cv′ = cvFlo η₀} (≅ᴵ-refl η₀) nz))

growT : ∀ {φ₋ φ′ η₋ a η′} {D₋ : Cz φ₋} {D′ : Cz φ′} {cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} →
        Ctxᶜ D′ → D₋ ≈ᶜ D′ → NZ η₋ → η₋ ≅ᴵ a → (q : a <ᴵ η′) →
        (G₋ : Goodᴺ (toZ (runᶜ D₋ (tl φ₋ cv₋ (Ωˢ η₋))))) (G′ : Goodᴺ (toZ (runᶜ D′ (tl φ′ cv′ (Ωˢ η′))))) → lvG G₋ ≺ᴵ lvG G′
growT {φ′ = φ′} {η₋ = η₋} {a = a} {η′ = η′} {D₋ = D₋} {D′ = D′} {cv₋ = cv₋} {cv′ = cv′} cD o nz e q G₋ G′ =
  ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ S)) e₃)
           (toLevel-≺ (forceᴺ-HS _ (proj₁ S)) (forceᴺ-HS _ G′) (⊑≺ (proj₂ S)))
  where
  lT : ∀ {L} → Ev L φ′ → Ev L (flo η′)
  lT = lr η′ cv′
  lS : ∀ {L} → Ev L φ′ → Ev L (flo (suc a))
  lS v = λ x → cv′ v (τ q x)
  lA : ∀ {L} → Ev L φ′ → Ev L (flo a)
  lA v = toFlo a (λ x → cv′ v (τ q (suc x)))
  nzη′ : NZ η′
  nzη′ = NZ-of q
  rD = ≈ᶜ-reflʳ o
  dT = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ lT sub-id rD) (R-root {cv = cv′} {cv′ = cvFlo η′} (≅ᴵ-refl η′) nzη′))
  G₂ = Goodᴺ-tr dT G′
  L = Ω<ᴱ (≅ᴵ-refl a) q {O = tlo (wkC lS sub-id D′)} {O′ = tlo (wkC lT sub-id D′)} (tlo (wk≈ lS sub-id lT sub-id rD)) G₂
  S = Ω-strict a {O = tlo (wkC lA sub-id D′)} {O′ = tlo (wkC lS sub-id D′)} (tlo (wk≈ lA sub-id lS sub-id rD)) (Ctx-wkC D′ cD) (proj₁ L)
  e₃ = forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ lA sub-id o) (R-root {cv = cv₋} {cv′ = cvFlo a} e nz))) G₋ (proj₁ S)
  ⊑≺ : forceᴺ _ (proj₁ S) ≺ forceᴺ _ (proj₁ L) → forceᴺ _ (proj₁ S) ≺ forceᴺ _ G′
  ⊑≺ h = ≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dT) G₂ G′) (proj₂ L h)

t₁ : Q h₀ zero (fz ⊔ fk zero) (κ Fl)
t₁ = tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))

gη : ∀ η → Q h₀ zero (fz ⊔ fk η) (κ Fl)
gη η = tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η)

rt₁ : Rq h₀ zero zero t₁ t₁
rt₁ = R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅))

rgη : ∀ η η′ → η ≅ᴵ η′ → Rq h₀ zero zero (gη η) (gη η′)
rgη η η′ d = R-tlΩ d (⊔∼ (∼ᶠ-refl fz) (fk∼ d))

𝟏⊑t₁ : 𝟏q zero ⊑ᵀ t₁
𝟏⊑t₁ = qi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d))))

ch₀ᵀ : ∀ {C : Cz (fz ⊔ fk zero)} → 𝓥 C → (G : Goodᴺ (toZ (runᶜ C t₁))) → ∀ {C′ : Cz (fz ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ (lvG G) C′
ch₀ᵀ {C} x G {C′} x′ o = br-mk x′ brB (suc zero) (fz ⊔ fk zero) proj₂ C (≈ᶜ-sym o) G (≅ᴵ-refl _) tt two
  where
  two : suc zero ≺ᴵ lvG G
  two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (Twᵀ C x rt₁ 𝟏⊑t₁ G)
  z₁ : zero <ᴵ lvG G
  z₁ = zlt (read1ᵀ C x t₁ rt₁ 𝟏⊑t₁ G)
  brB : ∀ {b} → b ≺ᴵ lvG G → CQ C′ b
  brB {b = zero} h {D = D} d t rt fl G′ = read1ᵀ D (≈Ctxᶜ d x′) t rt (fl (s≅ z≅ z≅) (≅→⊑ᴱ (s≅ z≅ z≅))) G′
  brB {b = suc b} h@(via e q) d t rt fl G′ = rd tt (≈ᶜ-sym (≈ᶜ-trans d o)) G h t (fl (Ωˢ-refl (suc zero)) (ω1b e q z₁ tt)) G′
  brB {b = lim f s} h@(via e q) d t rt fl G′ = rd tt (≈ᶜ-sym (≈ᶜ-trans d o)) G h t (fl (Ωˢ-refl (suc zero)) (ω1b e q z₁ tt)) G′

chSᵀ : ∀ η {C : Cz (fz ⊔ fk η)} → Brᵀ η C → (G : Goodᴺ (toZ (runᶜ C (gη η)))) → ∀ {C′ : Cz (fz ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ (lvG G) C′
chSᵀ η {C} B G {C′} x′ o = br-mk x′ brN η (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) C (≈ᶜ-sym o) G (≅ᴵ-refl _) nzη gr
  where
  nz≺ : ∀ {a b} → a ≺ᴵ b → NZ b
  nz≺ (via e q) = NZ-of q
  nzη : NZ η
  nzη = nz≺ (h₋ B)
  grr : η₋ B ≺ᴵ η → lvG (G₋ B) ≺ᴵ lvG G
  grr (via e′ q) = growT (cxB B) (o₋ B) (nz₋ B) e′ q (G₋ B) G
  gr : η ≺ᴵ lvG G
  gr = ≺ᴵ-respˡ (eη B) (grr (h₋ B))
  brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQ C′ b′
  brN {b′} h {D = D} d t rt fl G′ = go gr h
    where
    dC : D ≈ᶜ C
    dC = ≈ᶜ-trans d o
    go : η ≺ᴵ lvG G → b′ ≺ᴵ lvG G → suc b′ ⊑ᴵ lvG G′
    go (via ex qx) h′@(via eb qb) with <ᴵ-dec qb qx
    ... | injᵃ s = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) dC t rt fl G′
    ... | injᵇ s = rd nzη (≈ᶜ-sym dC) G h′ t (fl (Ωˢ-refl _) (Ωvia (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym eb))))) G′
    ... | injᶜ c = rd nzη (≈ᶜ-sym dC) G h′ t (fl (Ωˢ-refl _) (≅→⊑ᴱ (Ωˢ-≅ (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym eb)))))) G′

BrCast : ∀ {η η′} {C : Cz (fz ⊔ fk η)} {C′ : Cz (fz ⊔ fk η′)} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ η C → Brᵀ η′ C′
BrCast eq x′ o B = br-mk x′ (λ h d → br B (≺ᴵ-respʳ h (≅ᴵ-sym eq)) (≈ᶜ-trans d o)) (η₋ B) (φ₋ B) (cv₋ B) (D₋ B) (≈ᶜ-trans (o₋ B) (≈ᶜ-sym o)) (G₋ B)
                         (≅ᴵ-trans (≅ᴵ-sym eq) (eη B)) (nz₋ B) (≺ᴵ-respʳ (h₋ B) eq)

hzη : ∀ η {K} (q : InF K (fz ⊔ fk η)) {X} → η ≅ᴵ zero → Dem X q
hzη η (inr ink) e = inj₂ e

gg₀ : ∀ {g} η → Gq g h₀ zero (Brᵀ η) (gη η)
gg₀ zero = rootΩ zero (λ e q → proj₂ e (suc q)) (λ B → cxB B , tt) (hzη zero)
gg₀ (suc j) = rootΩ (suc j) (λ e q → proj₂ e (suc q)) (λ {C} B → cxB B , vis (Ctx-wkC C (cxB B)) (λ {b} h t et fl G →
  br B h {D = wkC (λ v → toFlo j (λ q → proj₂ v (suc (suc q)))) sub-id C} (≈ᶜ-wkˡ _ sub-id (ctxᶜ-refl C (cxB B))) (tl (flo j) (cvFlo j) t) (R-tl et) (λ ex u → tl-cong (fl ex u)) G)) (hzη (suc j))
gg₀ (lim f s) = rootΩ (lim f s) (λ e q → proj₂ e (suc q)) (λ {C} B → cxB B , λ n → vis (Ctx-wkC C (cxB B)) (λ { {b} (via e q) t et fl G →
  br B (via e (lim n q)) {D = wkC (λ v → toFlo (f n) (λ q₁ → proj₂ v (suc (lim n q₁)))) sub-id C} (≈ᶜ-wkˡ _ sub-id (ctxᶜ-refl C (cxB B))) (tl (flo (f n)) (cvFlo (f n)) t) (R-tl et) (λ ex u → tl-cong (fl ex u)) G })) (hzη (lim f s))

gt₀ : ∀ {g} → Gq g h₀ zero 𝓥 t₁
gt₀ = rootΩ (suc zero) proj₂ (λ {C} x → x , vis (Ctx-wkC C x) (λ
        { {b} (via e zero) t et fl G → ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 (tlo (wkC (λ v → toFlo zero (λ q → proj₂ v (suc q))) sub-id C)) (Ctx-wkC C x) t et (fl (s≅ z≅ z≅) (Ω1ᴱ b)) G)
        ; (via e (suc ())) t et fl G })) (λ q ())

nz⊑ : ∀ {a} → suc zero ⊑ᴵ a → NZ a
nz⊑ (s⊑ e q) = NZ-of q

Ω̇G₀ : ∀ {g} → Gq g h₀ zero {Fl} 𝓥 (rowB {h₀})
Ω̇G₀ = gclo 𝓥 (λ c → c) (λ x o _ → x) (λ η C → Brᵀ η C) BrCast gt₀ gg₀ rt₁ rgη
  (λ η h → rootmono tt (nz⊑ h) h)
  (λ η η′ h u → rootmono (nz⊑ h) (nz⊑ (⊑ᴵ-trans h u)) u)
  (λ c G ())
  (λ η c G ())
  ch₀ᵀ chSᵀ
```
