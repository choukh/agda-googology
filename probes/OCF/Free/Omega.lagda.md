# 无记号主线 (十九): `Ω̇G`

> **`Ω̇G : ∀ α → Gᵀ α 𝓥 (Ω̇ α)`, 对一切层号, 一个定理.**
> 脚本从 [UniformNF5Omega](../Align/UniformNF5Omega.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Omega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; trˢ; tr⁻ˢ)
open import OCF.Free.Eq using (≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; toZ-≅; Ωˢ-≅; Ωˢ-refl; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᴵ→⊑ᴵ; addˢ-≅; self-trˢ; self-tr⁻ˢ; tr⁻ˢ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; ⊔∼; fk∼; flo; cvFlo; toFlo)
open import OCF.Free.Aux using (one⁰)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Force using (Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Base
open import OCF.Free.Rules
open import OCF.Free.Strict
open import OCF.Free.Class
open import OCF.Free.ClassF
open import OCF.Free.Good
open import OCF.Free.Tail
```

```agda
open Ord-Ord using (iter)
open RestrO
```

## §1 上下文条件沿相似传递, 层号 $\succ 1$

```agda
≈Ctx : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → Ctx O′ → Ctx O
≈Ctxᶜ : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → Ctxᶜ C′ → Ctxᶜ C
≈Ctx idO c = tt
≈Ctx (tlo o) c = ≈Ctxᶜ o c
≈Ctx (addo {ℓ′ = ℓ′} {a = a} {a′ = a′} o k e) (afl ea one nz , c) = afl (≅ˢ-reflˡ e) one′ (NZ-e k nz) , ≈Ctx o c
  where
  one′ : 𝟏 ⊑ᴱ a
  one′ = ⊑ᴱ-≅ʳ (fl-tr⁻ k (s≅ z≅ z≅) one) (tr⁻ˢ-≅ k (≅ˢ-sym e))
≈Ctx (tro o) c = ≈Ctx o c
≈Ctx (tr⁻o o) c = ≈Ctx o c
≈Ctxᶜ (top o) c = ≈Ctx o c
≈Ctxᶜ (pa r o) (w , c) = w , ≈Ctxᶜ o c
≈Ctxᶜ (pψ o) c = ≈Ctxᶜ o c
≈Ctxᶜ (pι o) c = ≈Ctxᶜ o c
≈Ctxᶜ (ptr o) c = ≈Ctxᶜ o c
≈Ctxᶜ (ptr⁻ o) c = ≈Ctxᶜ o c

𝟐 : Ordˢ zero
𝟐 = Ord₊ˢ.suc 𝟏

𝟏⊑𝟐 : 𝟏 ⊑ᴱ 𝟐
𝟏⊑𝟐 = suc-rᴱ (≅→⊑ᴱ (s≅ z≅ z≅))

Twᵛ : ∀ {k} (O : Obs k) → NZ k → Ctx O → ∀ {y : Ordˢ k} → y ≅ˢ y → 𝟏 ⊑ᴱ y → (G : Goodᴺ (toZ (run O y))) → one⁰ ≺ forceᴺ _ G
V₀ : (O : Obs zero) → Ctx O → ∀ {y : Ordˢ zero} → y ≅ˢ y → 𝟐 ⊑ᴱ y → (G : Goodᴺ (toZ (run O y))) → one⁰ ≺ forceᴺ _ G
Twᵀ : ∀ {c φ} (C : Cx c φ) → Ctxᶜ C → ∀ {y : O c φ} → Rᵒ c c y y → 𝟏ᵀ ⊑ᵀ y → (G : Goodᴺ (toZ (runᶜ C y))) → one⁰ ≺ forceᴺ _ G
Twᵛ idO () c ey one G
Twᵛ (tlo {k = k} C) nz c {y = y} ey one G = Twᵀ C c {y = tl (flo k) (cvFlo k) y} (R-tl ey) (tl-cong one) G
Twᵛ (addo O a σ) nz (afl ea oa nzA , c) {y = y} ey one G = Twᵛ O nzA c {y = addˢ a σ y} (addˢ-≅ (≅ᴵ-refl _) ea ey) (add-floorᴱ {σ = σ} y oa ey) G
Twᵛ (tro O e) nz c {y = y} ey one G = Twᵛ O (NZ-e′ e nz) c {y = trˢ e y} (self-trˢ e ey) (fl-tr e (s≅ z≅ z≅) one) G
Twᵛ (tr⁻o O e) nz c {y = y} ey one G = Twᵛ O (NZ-e e nz) c {y = tr⁻ˢ e y} (self-tr⁻ˢ e ey) (fl-tr⁻ e (s≅ z≅ z≅) one) G
V₀ idO c ey two G = proj₂ L (h2N (proj₁ L))
  where L = two idO G
V₀ (tlo C) c {y = y} ey two G = Twᵀ C c {y = tl (flo zero) (cvFlo zero) y} (R-tl ey) (tl-cong (⊑ᴱ-trans 𝟏⊑𝟐 two)) G
V₀ (addo O a σ) (afl ea oa nzA , c) {y = y} ey two G = Twᵛ O nzA c {y = addˢ a σ y} (addˢ-≅ (≅ᴵ-refl _) ea ey) (add-floorᴱ {σ = σ} y oa ey) G
V₀ (tro O z≅) c {y = y} ey two G = V₀ O c {y = trˢ z≅ y} (self-trˢ z≅ ey) (fl-tr z≅ (s≅ z≅ (s≅ z≅ z≅)) two) G
V₀ (tr⁻o O z≅) c {y = y} ey two G = V₀ O c {y = tr⁻ˢ z≅ y} (self-tr⁻ˢ z≅ ey) (fl-tr⁻ z≅ (s≅ z≅ (s≅ z≅ z≅)) two) G
Twᵀ (top {i = zero} O ev p) c {y = y} ry one G = V₀ O c {y = ψ̄ y ev p} (R→≈ ry ev p ev p z≅) (S1ᵀ one) G
Twᵀ (top {i = suc i} O ev p) c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ y ev p} (R→≈ ry ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᵀ (top {i = lim f s} O ev p) c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ y ev p} (R→≈ ry ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᵀ (pa W C) (w , c) {y = y} ry one G = Twᵀ C c {y = W ⊕ y} (R-⊕ (∼ᶠ-refl _) (WFl.rW w) ry) (B1ᵀ ry (WFl.oneW w)) G
Twᵀ (pψ {t = t} q C) c {y = y} ry one G = Twᵀ C c {y = ψᵒ q y} (R-ψ q q (≅ᴵ-refl _) ry) (P0ᵀ {q = q} ry (𝟏⊑Ω̇ t)) G
Twᵀ (pι q C) c {y = y} ry one G = Twᵀ C c {y = ι q y} (R-ι q q ry) (ι-cong {q = q} one) G
Twᵀ (ptr e C) c {y = y} ry one G = Twᵀ C c {y = trO e y} (R-tr₂ e e ry) (trᵀ-cong {e = e} {e′ = e} one) G
Twᵀ (ptr⁻ e C) c {y = y} ry one G = Twᵀ C c {y = tr⁻O e y} (R-tr⁻₂ e e ry) (tr⁻ᵀ-cong {e = e} {e′ = e} one) G
```

## §2 根地板非紧的 $\Omega_\eta$

```agda
lr : ∀ {φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) {L} → Ev L φ → Ev L (flo η)
lr η cv v = toFlo η (cv v)

R-root : ∀ {c η η′ φ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L (flo η′) → Simᴵ η′ L} → η ≅ᴵ η′ → NZ η → Rᵒ c c (tl φ cv (Ωˢ η)) (tl (flo η′) cv′ (Ωˢ η′))
R-root (s≅ e) nz = ri e (λ x y d → rwk (R-tl d))
R-root (l≅ h) nz = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

rootmono : ∀ {c a b φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ a L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ b L} → NZ a → NZ b → a ⊑ᴵ b → tl {c = c} φ cv (Ωˢ a) ⊑ᵗ tl {c = c} φ′ cv′ (Ωˢ b)
rootmono {a = a} {b = b} {cv = cv} {cv′ = cv′} na nb u {C} {C′} o G G′ =
  ⊑-trans (≅→⊑ (forceᴺ-≅ dA G GA)) (⊑-trans (tl-congᵒ (Ω-monoᵒ u) (wk≈ (lr a cv) (lr b cv′) o) GA GB) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dB) GB G′)))
  where
  dA = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr a cv) (≈ᶜ-reflˡ o)) (R-root {cv′ = cvFlo a} (≅ᴵ-refl a) na))
  dB = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr b cv′) (≈ᶜ-reflʳ o)) (R-root {cv′ = cvFlo b} (≅ᴵ-refl b) nb))
  GA = Goodᴺ-tr dA G
  GB = Goodᴺ-tr dB G′

VisΩ : ∀ {c φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) → Cx c φ → Set
VisΩ zero      cv C = ⊤
VisΩ (suc j)   cv C = Vis (suc j) (tlo (wkC (λ v → toFlo j (λ q → cv v (suc q))) C))
VisΩ (lim f s) cv C = ∀ n → Vis (f n) (tlo (wkC (λ v → toFlo (f n) (λ q → cv v (lim n q))) C))

hlV : ∀ {c} k → Hl {c} k (λ E → 𝓥 E × Vis k (tlo E)) (Vis k)
hlV zero = vis tt (λ { (via _ ()) })
hlV (suc k) = proj₂
hlV (lim f s) = proj₂

hlI : ∀ {c φ j} (le : ∀ {L} → Ev L φ → Ev L (flo j)) (𝓔 : ClT c φ) → Hl {c} j (λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le C))) (Inp j ((λ C → tlo (wkC le C)) ⟪ 𝓔 ⟫))
hlI {j = zero} le 𝓔 = refl
hlI {j = suc j} le 𝓔 (x , C , c , o) = x , C , c , tlo o
hlI {j = lim f s} le 𝓔 (x , C , c , o) = x , C , c , tlo o

rootΩ : ∀ {c φ} η (cv : ∀ {L} → Ev L φ → Simᴵ η L) {𝓖 : ClT c φ} → (∀ {C} → 𝓖 C → Ctxᶜ C × VisΩ η cv C) → (∀ {K} (q : InF K φ) {X} → η ≅ᴵ zero → Dem X q) → Gᵀ c 𝓖 (tl φ cv (Ωˢ η))
rootΩ {φ = φ} zero cv H hz₀ = gs 𝓥 (λ c → proj₁ (H c)) g0 (λ _ f → cxoᵀ f) (λ x o _ → x) (λ _ _ q → hz₀ q z≅)
rootΩ {c = c} {φ = φ} (suc j) cv {𝓖 = 𝓖} H hz₀ =
  gi (λ C → Ctxᶜ C × VisΩ (suc j) cv C) H (λ C → tlo (wkC le C))
     (λ {C} (x , v) u eu → subst (λ w → run (tlo (wkC le C)) u ≅ˢ w) (run-wkC le C (tl (flo j) (cvFlo j) u))
          (run-≅ (tlo (ctxᶜ-refl (wkC le C) (Ctx-wkC C x))) eu))
     (λ 𝓔 inc″ z ez g →
        gw (λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le C)))
           (λ {C} c₁ → Ctx-wkC C (proj₁ (inc″ c₁)) , C , c₁ , ctxᶜ-refl (wkC le C) (Ctx-wkC C (proj₁ (inc″ c₁))))
           (TL {𝓖 = λ E → 𝓥 E × (Σ _ λ C → 𝓔 C × (E ≈ᶜ wkC le C))} {𝓧 = Inp j ((λ C → tlo (wkC le C)) ⟪ 𝓔 ⟫)} (hlI le 𝓔) proj₁ g ez))
     (λ (x , v) → v)
     (λ {C} {C′} (x , v) (aboveV cx′ wrap) → cx′ , vis (Ctx-wkC C′ cx′) (λ {b} h t et fl G →
        at≡ (sym (run-wkC le C′ (tl (flo j) (cvFlo j) t))) {Q = λ X → suc b ⊑ᴵ X}
          (λ G₁ →
            let Wp = wrap (owk le (tl (flo j) (cvFlo j) t)) (rwk (R-tl et))
                u = proj₁ Wp
                eu = proj₁ (proj₂ Wp)
                fu = proj₁ (proj₂ (proj₂ Wp))
                d = proj₂ (proj₂ (proj₂ Wp))
            in pull d (cp v h u eu (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) fu)) G₁) G))
     (λ {C} {C′} x o (_ , v) → x , Vis-≈ (Ctx-wkC C x) (tlo (wk≈ le le o)) v)
     (λ h → wk-lᵗ (wk-rᵗ (tl-congᵒ h)))
     (λ d → rwk (R-tl d))
  where
  le : ∀ {L} → Ev L φ → Ev L (flo j)
  le v = toFlo j (λ q → cv v (suc q))
rootΩ {c = c} {φ = φ} (lim f s) cv {𝓖 = 𝓖} H hz₀ =
  gl (λ n → gw (λ E → 𝓥 E × Vis (f n) (tlo E))
              (λ {C} c₁ → Ctx-wkC C (proj₁ (H c₁)) , proj₂ (H c₁) n)
              (TL {𝓖 = λ E → 𝓥 E × Vis (f n) (tlo E)} {𝓧 = Vis (f n)} (hlV (f n)) proj₁ (Ωg (f n)) (Ωˢ-refl (f n))))
     (λ n → wk-lᵗ (wk-rᵗ (tl-congᵒ (Ω-monoᵒ (s n)))))
```

## §3 $\dot\Omega_0$: 闭包的守卫

```agda
FlT : ∀ {c χ} → Ordᴵ → O c χ → Set
FlT {c} b t = ∀ {k₀} {x : Ordˢ k₀} → x ≅ˢ x → x ⊑ᴱ Ωˢ b → tl {c = c} (flo k₀) (cvFlo k₀) x ⊑ᵀ t

CQ : ∀ {c ψ} → Cx c ψ → Ordᴵ → Set
CQ {c} C b = ∀ {χ} {D : Cx c χ} → D ≈ᶜ C → (t : O c χ) → Rᵒ c c t t → FlT b t → (G : Goodᴺ (toZ (runᶜ D t))) → suc b ⊑ᴵ lvG G

record Brᵀ {c ψ} (η : Ordᴵ) (C : Cx c ψ) : Set where
  constructor br-mk
  field
    cxB : Ctxᶜ C
    br  : ∀ {b} → b ≺ᴵ η → CQ C b
    η₋  : Ordᴵ
    φ₋  : Flr
    cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L
    D₋  : Cx c φ₋
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

rd : ∀ {c φ₀ χ η₀ b} {D₀ : Cx c φ₀} {D : Cx c χ} {cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ η₀ L} → NZ η₀ → D₀ ≈ᶜ D →
     (G₀ : Goodᴺ (toZ (runᶜ D₀ (tl φ₀ cv₀ (Ωˢ η₀))))) → b ≺ᴵ lvG G₀ → (t : O c χ) → tl {c = c} (flo η₀) (cvFlo η₀) (Ωˢ η₀) ⊑ᵀ t → (G : Goodᴺ (toZ (runᶜ D t))) → suc b ⊑ᴵ lvG G
rd {η₀ = η₀} {D₀ = D₀} {cv₀ = cv₀} nz o G₀ h t fl G =
  s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                         (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
  where
  L = fl (≈ᶜ-wkˡ (lr η₀ cv₀) o) G
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (lr η₀ cv₀) (≈ᶜ-reflˡ o)) (R-root {cv = cv₀} {cv′ = cvFlo η₀} (≅ᴵ-refl η₀) nz))

growT : ∀ {c φ₋ φ′ η₋ a η′} {D₋ : Cx c φ₋} {D′ : Cx c φ′} {cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} →
        Ctxᶜ D′ → D₋ ≈ᶜ D′ → NZ η₋ → η₋ ≅ᴵ a → (q : a <ᴵ η′) →
        (G₋ : Goodᴺ (toZ (runᶜ D₋ (tl φ₋ cv₋ (Ωˢ η₋))))) (G′ : Goodᴺ (toZ (runᶜ D′ (tl φ′ cv′ (Ωˢ η′))))) → lvG G₋ ≺ᴵ lvG G′
growT {c = c} {φ′ = φ′} {η₋ = η₋} {a = a} {η′ = η′} {D₋ = D₋} {D′ = D′} {cv₋ = cv₋} {cv′ = cv′} cD o nz e q G₋ G′ =
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
  dT = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ lT rD) (R-root {cv = cv′} {cv′ = cvFlo η′} (≅ᴵ-refl η′) nzη′))
  G₂ = Goodᴺ-tr dT G′
  L = Ω<ᴱ (≅ᴵ-refl a) q {O = tlo (wkC lS D′)} {O′ = tlo (wkC lT D′)} (tlo (wk≈ lS lT rD)) G₂
  S = Ω-strict a {O = tlo (wkC lA D′)} {O′ = tlo (wkC lS D′)} (tlo (wk≈ lA lS rD)) (Ctx-wkC D′ cD) (proj₁ L)
  e₃ = forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ lA o) (R-root {cv = cv₋} {cv′ = cvFlo a} e nz))) G₋ (proj₁ S)
  ⊑≺ : forceᴺ _ (proj₁ S) ≺ forceᴺ _ (proj₁ L) → forceᴺ _ (proj₁ S) ≺ forceᴺ _ G′
  ⊑≺ h = ≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dT) G₂ G′) (proj₂ L h)
```

```agda
t₁ : O zero (fz ⊔ fk zero)
t₁ = tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))

gη : ∀ η → O zero (fz ⊔ fk η)
gη η = tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η)

rt₁ : Rᵒ zero zero t₁ t₁
rt₁ = R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅))

rgη : ∀ η η′ → η ≅ᴵ η′ → Rᵒ zero zero (gη η) (gη η′)
rgη η η′ d = R-tlΩ d (⊔∼ (∼ᶠ-refl fz) (fk∼ d))

𝟏⊑t₁ : 𝟏ᵀ ⊑ᵀ t₁
𝟏⊑t₁ = oi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d))))

ch₀ᵀ : ∀ {C : Cx zero (fz ⊔ fk zero)} → 𝓥 C → (G : Goodᴺ (toZ (runᶜ C t₁))) → ∀ {C′ : Cx zero (fz ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ (lvG G) C′
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

chSᵀ : ∀ η {C : Cx zero (fz ⊔ fk η)} → Brᵀ η C → (G : Goodᴺ (toZ (runᶜ C (gη η)))) → ∀ {C′ : Cx zero (fz ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ (lvG G) C′
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

BrCast : ∀ {η η′} {C : Cx zero (fz ⊔ fk η)} {C′ : Cx zero (fz ⊔ fk η′)} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → Brᵀ η C → Brᵀ η′ C′
BrCast eq x′ o B = br-mk x′ (λ h d → br B (≺ᴵ-respʳ h (≅ᴵ-sym eq)) (≈ᶜ-trans d o)) (η₋ B) (φ₋ B) (cv₋ B) (D₋ B) (≈ᶜ-trans (o₋ B) (≈ᶜ-sym o)) (G₋ B)
                         (≅ᴵ-trans (≅ᴵ-sym eq) (eη B)) (nz₋ B) (≺ᴵ-respʳ (h₋ B) eq)

hzη : ∀ η {K} (q : InF K (fz ⊔ fk η)) {X} → η ≅ᴵ zero → Dem X q
hzη η (inr ink) e = inj₂ e

gg₀ : ∀ η → Gᵀ zero (Brᵀ η) (gη η)
gg₀ zero = rootΩ zero (λ e q → proj₂ e (suc q)) (λ B → cxB B , tt) (hzη zero)
gg₀ (suc j) = rootΩ (suc j) (λ e q → proj₂ e (suc q)) (λ {C} B → cxB B , vis (Ctx-wkC C (cxB B)) (λ {b} h t et fl G →
  br B h {D = wkC (λ v → toFlo j (λ q → proj₂ v (suc (suc q)))) C} (≈ᶜ-wkˡ _ (ctxᶜ-refl C (cxB B))) (tl (flo j) (cvFlo j) t) (R-tl et) (λ ex u → tl-cong (fl ex u)) G)) (hzη (suc j))
gg₀ (lim f s) = rootΩ (lim f s) (λ e q → proj₂ e (suc q)) (λ {C} B → cxB B , λ n → vis (Ctx-wkC C (cxB B)) (λ { {b} (via e q) t et fl G →
  br B (via e (lim n q)) {D = wkC (λ v → toFlo (f n) (λ q₁ → proj₂ v (suc (lim n q₁)))) C} (≈ᶜ-wkˡ _ (ctxᶜ-refl C (cxB B))) (tl (flo (f n)) (cvFlo (f n)) t) (R-tl et) (λ ex u → tl-cong (fl ex u)) G })) (hzη (lim f s))

gt₀ : Gᵀ zero 𝓥 t₁
gt₀ = rootΩ (suc zero) proj₂ (λ {C} x → x , vis (Ctx-wkC C x) (λ
        { {b} (via e zero) t et fl G → ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 _ (Ctx-wkC C x) t et (fl (s≅ z≅ z≅) (Ω1ᴱ b)) G)
        ; (via e (suc ())) t et fl G })) (λ q ())

nz⊑ : ∀ {a} → suc zero ⊑ᴵ a → NZ a
nz⊑ (s⊑ e q) = NZ-of q

Ω̇G₀ : Gᵀ zero {Fl} 𝓥 (Ω̇ zero)
Ω̇G₀ = gclo 𝓥 (λ c → c) (λ η C → Brᵀ η C) BrCast gt₀ gg₀ rt₁ rgη
  (λ η h → rootmono tt (nz⊑ h) h)
  (λ η η′ h u → rootmono (nz⊑ h) (nz⊑ (⊑ᴵ-trans h u)) u)
  (λ c G ())
  (λ η c G ())
  ch₀ᵀ chSᵀ
```

## §3′ $\dot\Omega$ 对层号单调

```agda
◃-tr : ∀ {a b c} → a ◃ b → b ◃ c → a ◃ c
◃-tr r zero      = suc r
◃-tr r (suc q)   = suc (◃-tr r q)
◃-tr r (self n)  = lim n r
◃-tr r (lim n q) = lim n (◃-tr r q)

Ωstep : ∀ {b c} (r₀ : b ◃ c) (r : suc b ◃ c) → ι r₀ (Ω̇ b) ⊑ᵀ ι r (Ω̇ (suc b))
Ωstep {b} {c} r₀ r = Ω-rᵀ (λ ξ z rz f →
  subst (λ w → ι r₀ (Ω̇ b) ⊑ᵀ ι r (owk proj₁ (ι zero w))) (sym (out-intoU (<→◃ (<◃ {k = b} zero r)) z))
    (wk-rᵀ (⊑ᵀ-Rʳ (ι-cong {q = r₀} (f (RΩ̇ (≅ᴵ-refl b)) (R→⊑ᵀ (RΩ̇ (≅ᴵ-refl b))))) (R-ι r₀ r (R-ιʳ zero rz)))))

Ωlim : ∀ {f s c} n (r₀ : f n ◃ c) (r : lim f s ◃ c) → ι r₀ (Ω̇ (f n)) ⊑ᵀ ι r (Ω̇ (lim f s))
Ωlim n r₀ r = lim-rᵀ n (R→⊑ᵀ (R-ι r₀ r (R-ιʳ (self n) (RΩ̇ (≅ᴵ-refl _)))))

Ωz : ∀ {c} b (r : zero ◃ c) (r′ : b ◃ c) → ι r (Ω̇ zero) ⊑ᵀ ι r′ (Ω̇ b)
Ωz zero r r′ = R→⊑ᵀ (R-ι r r′ (RΩ̇ z≅))
Ωz (suc b) r r′ = ⊑ᵀ-trans (Ωz b r (◃-tr zero r′)) (Ωstep (◃-tr zero r′) r′)
Ωz (lim g s) r r′ = ⊑ᵀ-trans (Ωz (g 0) r (◃-tr (self 0) r′)) (Ωlim 0 (◃-tr (self 0) r′) r′)

Ωs : ∀ {a₀ a″ b c} → a₀ ≅ᴵ a″ → a″ <ᴵ b → (r : suc a₀ ◃ c) (r′ : b ◃ c) → ι r (Ω̇ (suc a₀)) ⊑ᵀ ι r′ (Ω̇ b)
Ωs e zero r r′ = R→⊑ᵀ (R-ι r r′ (RΩ̇ (s≅ e)))
Ωs e (suc q) r r′ = ⊑ᵀ-trans (Ωs e q r (◃-tr zero r′)) (Ωstep (◃-tr zero r′) r′)
Ωs e (lim n q) r r′ = ⊑ᵀ-trans (Ωs e q r (◃-tr (self n) r′)) (Ωlim n (◃-tr (self n) r′) r′)

⊑ᵗ-Rˡ : ∀ {c φ ψ} {x x′ : O c φ} {y : O c ψ} → Rᵒ c c x x′ → x′ ⊑ᵗ y → x ⊑ᵗ y
⊑ᵗ-Rˡ e h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ d G (Goodᴺ-tr d G))) (h o (Goodᴺ-tr d G) G′)
  where d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) e)

Ωm : ∀ {a b c} → a ⊑ᴵ b → (r : a ◃ c) (r′ : b ◃ c) → ι r (Ω̇ a) ⊑ᵗ ι r′ (Ω̇ b)
Ωm {b = b} z⊑ r r′ = ⊑ᵀ→ᵗ (R-ι r r (RΩ̇ z≅)) (Ωz b r r′)
Ωm (s⊑ e q) r r′ = ⊑ᵀ→ᵗ (R-ι r r (RΩ̇ (≅ᴵ-refl _))) (Ωs e q r r′)
Ωm (l⊑ k) r r′ = lim-lᵗ (λ n → ⊑ᵗ-Rˡ (R-ιʳ (◃-tr (self n) r) (R-ιˡ r (R-ιˡ (self n) (RΩ̇ (≅ᴵ-refl _))))) (Ωm (k n) (◃-tr (self n) r) r′))

mono-self : ∀ {f} (s : ∀ n → f n ⊑ᴵ f (suc n)) n → ι (self {f} {s} n) (Ω̇ (f n)) ⊑ᵗ ι (self {f} {s} (suc n)) (Ω̇ (f (suc n)))
mono-self s n = Ωm (s n) (self n) (self (suc n))
```

```agda
Ω̇G : ∀ c → Gᵀ c {Fl} 𝓥 (Ω̇ c)
Ω̇G zero = Ω̇G₀
Ω̇G (suc c) =
  gΩ (λ ξ → 𝓥) (λ ξ c₁ x o → x) (λ ξ D → pι zero (wkC proj₁ D))
     (λ ξ {C} x u ru → subst (λ v → runᶜ (pι zero (wkC proj₁ C)) u ≅ˢ v) (run-wkC proj₁ C (ι zero u))
          (runᶜ-≅ (ctxᶜ-refl (pι zero (wkC proj₁ C)) (Ctx-wkC C x)) ru))
     (λ 𝓔 inc″ ξ z rz g →
        gw (λ E → Ctxᶜ E × (Σ _ λ D → 𝓔 ξ D × (E ≡ wkC proj₁ D)))
           (λ {D} c₁ → Ctx-wkC D (inc″ ξ c₁) , D , c₁ , refl)
           (Iota zero {𝓖 = λ E → Ctxᶜ E × (Σ _ λ D → 𝓔 ξ D × (E ≡ wkC proj₁ D))} {𝓧 = (λ D → pι zero (wkC proj₁ D)) ⟪ 𝓔 ξ ⟫ᵀ}
                 (λ { (x , D , c₁ , refl) → x , D , c₁ , ctxᶜ-refl (pι zero (wkC proj₁ D)) x }) proj₁ g))
     (λ ξ {C} x → Ctx-wkC C x)
     (λ ξ x (aboveΩ cx′ wrap) → cx′)
     (λ ξ ξ′ x o _ → x)
     (λ u → wk-lᵗ (wk-rᵗ (ι-congᵗ {q = zero} u)))
     (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))
Ω̇G (lim f s) =
  gl (λ n → Iota (self n) {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Ω̇G (f n)))
     (λ n → mono-self s n)
```
