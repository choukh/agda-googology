# 阶梯去记号 (二十四): 塔上的 $\dot\Omega$

> 结论写在 [LadderNF](LadderNF.lagda.md). `Ω̇G g m k`: 一切 $m$, $k$, `Ω̇ m k` 都是 `Gq`. 高度 $n+1$ 的闭包守卫 `Brq` 与根层的 `Brᵀ` 同形: 读数是 "$\dot\Omega_b$ 之下层号 $\succeq b+1$", 增长由 `Ω↓≺` 给出, 下移由 `InvD` 读出. 无归纳于 $\theta$, $c$; 对 $m$ 的结构递归只是 $\dot\Omega$ 定义本身的结构. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFOmega where

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
open import OCF.Align.LadderNFTree
open import OCF.Align.LadderNFRel
open import OCF.Align.LadderNFCx
open import OCF.Align.LadderNFRules
open import OCF.Align.LadderNFRules2
open import OCF.Align.LadderNFRules3
open import OCF.Align.LadderNFStrict
open import OCF.Align.LadderNFStrict2
open import OCF.Align.LadderNFClass
open import OCF.Align.LadderNFClassF using (inp-map)
open import OCF.Align.LadderNFGood
open import OCF.Align.LadderNFVis
open import OCF.Align.LadderNFIota
open import OCF.Align.LadderNFAdd
open import OCF.Align.LadderNFTr
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Force using (forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Eq using (s-invˢ; l-invˢ; i-respˢ; u-reflˢ; tf; ŝ≅; ĉ≅; upˡ; upʳ)
open import OCF.Align.LadderNFClassF

open import OCF.Align.LadderNFTail
open import OCF.Align.LadderNFRead
open import OCF.Free.Aux using (one⁰)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; Ωˢ-≅; Ωˢ-refl)
open import OCF.Free.Floor using (⊔∼; fk∼)
open import OCF.Align.LadderNFClassF using (NZ-of)

open import OCF.Align.LadderNFRoot using (Ω̇G₀; one⊑; zlt; τ; ≺ᴵ-up; NZ-≅₁)
open import OCF.Align.LadderNFStrict3 using (Ω↓≺)
open import OCF.Align.LadderNFMono
open RestrQ
```

## §1 高度 $n$ 的闭包守卫

```agda
CD : ∀ n → Ordᴵ → Set
CD n k = Cx (suc n) zero Fl (upd (κ Fl) n (flo k))

CQq : ∀ n {ψ ρ} → Cx (suc n) zero ψ ρ → Ordᴵ → Set
CQq n C b = ∀ {k′} → k′ ≅ᴵ b → {D : CD n k′} → D ≈ᶜ C → (G : Goodᴺ (toZ (runᶜ D (ι↓ {α = zero} (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G

record Brq n {ψ ρ} (η : Ordᴵ) (C : Cx (suc n) zero ψ ρ) : Set where
  constructor br-mk
  field
    cxB : Ctxᶜ C
    br  : ∀ {b} → b ≺ᴵ η → CQq n C b
    η₋  : Ordᴵ
    D₋  : CD n η₋
    o₋  : D₋ ≈ᶜ C
    G₋  : Goodᴺ (toZ (runᶜ D₋ (ι↓ {α = zero} (Ω̇ n η₋))))
    eη  : η ≅ᴵ lvG G₋
    h₋  : η₋ ≺ᴵ η
open Brq

Ω↓lt : ∀ {n a a′ b} → a ≅ᴵ a′ → (q : a′ <ᴵ b) → ι↓ {n = n} {α = zero} (Ω̇ n a) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n b)
Ω↓lt {n} {a} {a′} {b} e q =
  ⊑ᵀ-transʷ (λ u → u) (⇑ (upd-map n (λ i u → u) (λ u {c} x → cvFlo b u (τ q x))))
    (⊑ᵀ-Rˡʷ (λ u → u) D↑s (R-ι↓ e (RΩ̇ n e)) Ωstep↓) (Ωs↓ (≅ᴵ-refl a′) q)

Ω↓via : ∀ {n a b} → a ≺ᴵ b → ι↓ {n = n} {α = zero} (Ω̇ n a) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n b)
Ω↓via (via e q) = Ω↓lt e q

rdq : ∀ {n η₀ k′ b} {D₀ : CD n η₀} {D : CD n k′} → D₀ ≈ᶜ D → (G₀ : Goodᴺ (toZ (runᶜ D₀ (ι↓ {α = zero} (Ω̇ n η₀))))) → b ≺ᴵ lvG G₀ →
      ι↓ {n = n} {α = zero} (Ω̇ n η₀) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n k′) → (G : Goodᴺ (toZ (runᶜ D (ι↓ {α = zero} (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G
rdq {n} {η₀} o G₀ h fl G =
  s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                         (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
  where
  L = fl o G
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) (R-ι↓ (≅ᴵ-refl η₀) (RΩ̇ n (≅ᴵ-refl η₀))))

growT : ∀ {n η₋ a η′} {D₋ : CD n η₋} {D′ : CD n η′} → Ctxᶜ D′ → D₋ ≈ᶜ D′ → η₋ ≅ᴵ a → (q : a <ᴵ η′) →
        (G₋ : Goodᴺ (toZ (runᶜ D₋ (ι↓ {α = zero} (Ω̇ n η₋))))) (G′ : Goodᴺ (toZ (runᶜ D′ (ι↓ {α = zero} (Ω̇ n η′))))) → lvG G₋ ≺ᴵ lvG G′
growT {n} {η₋} {a} {η′} {D₋} {D′} cD o e q G₋ G′ =
  ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ S)) e₃)
           (toLevel-≺ (forceᴺ-HS _ (proj₁ S)) (forceᴺ-HS _ G′) (proj₂ L (proj₂ S)))
  where
  lS : Sub (suc n) (upd (κ Fl) n (flo η′)) (upd (κ Fl) n (flo (suc a)))
  lS = ⇑ (upd-map n (λ i u → u) (λ u {c} x → cvFlo η′ u (τ q x)))
  lA : Sub (suc n) (upd (κ Fl) n (flo η′)) (upd (κ Fl) n (flo a))
  lA = ⇑ (upd-map n (λ i u → u) (λ u → toFlo a (λ x → cvFlo η′ u (τ q (suc x)))))
  rD = ≈ᶜ-reflʳ o
  L = Ωs↓ (≅ᴵ-refl a) q {C = wkC (λ u → u) lS D′} {C′ = D′} (≈ᶜ-wkˡ (λ u → u) lS rD) G′
  S = Ω↓≺ n a {C = wkC (λ u → u) lA D′} {C′ = wkC (λ u → u) lS D′} (wk≈ (λ u → u) lA (λ u → u) lS rD) (Ctx-wkC D′ cD) tt (proj₁ L)
  e₃ = forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (λ u → u) lA o) (R-ι↓ e (RΩ̇ n e)))) G₋ (proj₁ S)

brZ : ∀ {n ψ ρ} {C : Cx (suc n) zero ψ ρ} → Ctxᶜ C → CQq n C zero
brZ {n} x {k′} e {D} d G = read1ᵀ D (≈Ctxᶜ d x) (ι↓ (Ω̇ n k′)) (R-ι↓ (≅ᴵ-refl k′) (RΩ̇ n (≅ᴵ-refl k′))) (𝟏-D (𝟏⊑Ω̇ n k′)) G

lvG≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G₁ → lvG G ≅ᴵ lvG G₁
lvG≡ refl G = G , ≅ᴵ-refl _

ω1q : ∀ {n k′ x L} → k′ ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ x → ι↓ {n = n} {α = zero} (Ω̇ n (suc zero)) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n k′)
ω1q {n} {k′} e q z nx = go (⊑ᴵ-≅ʳ (one⊑ z q nx) (≅ᴵ-sym e))
  where
  go : suc zero ⊑ᴵ k′ → ι↓ {n = n} {α = zero} (Ω̇ n (suc zero)) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n k′)
  go (s⊑ z≅ r) = Ωs↓ z≅ r

ch₀q : ∀ {n} (uₒ : Sub (suc n) (κ Fl) (upd (κ Fl) n (flo (suc zero)))) {C : Cx (suc n) zero Fl (κ Fl)} → 𝓥 C →
       (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) uₒ (ι↓ {α = zero} (Ω̇ n (suc zero))))))) →
       ∀ {C′ : Cx (suc n) zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq n (lvG G) C′
ch₀q {n} uₒ {C} x G {C′} x′ o = br-mk x′ brB (suc zero) D₁ (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym o)) G₁ e₁ two
  where
  J = lvG≡ (run-wkC (λ u → u) uₒ C (ι↓ (Ω̇ n (suc zero)))) G
  G₁ = proj₁ J
  e₁ = proj₂ J
  D₁ = wkC (λ u → u) uₒ C
  rt₁ : Rq (suc n) zero zero (qwk (λ u → u) uₒ (ι↓ {α = zero} (Ω̇ n (suc zero)))) (qwk (λ u → u) uₒ (ι↓ {α = zero} (Ω̇ n (suc zero))))
  rt₁ = rwk (R-ι↓ (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _)))
  one₁ : 𝟏q zero ⊑ᵀ qwk (λ u → u) uₒ (ι↓ {α = zero} (Ω̇ n (suc zero)))
  one₁ = wk-rᵀ (𝟏-D (𝟏⊑Ω̇ n (suc zero)))
  two : suc zero ≺ᴵ lvG G
  two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (Twᵀ C x rt₁ one₁ G)
  z₁ : zero <ᴵ lvG G
  z₁ = zlt (read1ᵀ C x _ rt₁ one₁ G)
  brB : ∀ {b} → b ≺ᴵ lvG G → CQq n C′ b
  brB {b = zero} h e d G′ = brZ x′ e d G′
  brB {b = suc b} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′
  brB {b = lim f s} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′

LLq : ∀ n η → Sub (suc n) (upd (κ Fl) n (fz ⊔ fk η)) (upd (κ Fl) n (flo η))
LLq n η = upd-sub n (λ i q e → e) (λ e → toFlo η (λ q → proj₂ e (suc q)))

chSq : ∀ {n} η {C : Cx (suc n) zero Fl (upd (κ Fl) n (fz ⊔ fk η))} → Brq n η C →
       (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) (LLq n η) (ι↓ {α = zero} (Ω̇ n η)))))) →
       ∀ {C′ : Cx (suc n) zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq n (lvG G) C′
chSq {n} η {C} B G {C′} x′ o = br-mk x′ brN η D₁ (≈ᶜ-wkˡ (λ u → u) (LLq n η) (≈ᶜ-sym o)) G₁ e₁ (≺ᴵ-respʳ gr (≅ᴵ-sym e₁))
  where
  J = lvG≡ (run-wkC (λ u → u) (LLq n η) C (ι↓ (Ω̇ n η))) G
  G₁ = proj₁ J
  e₁ = proj₂ J
  D₁ = wkC (λ u → u) (LLq n η) C
  grr : η₋ B ≺ᴵ η → lvG (G₋ B) ≺ᴵ lvG G₁
  grr (via e′ q) = growT (Ctx-wkC C (cxB B)) (≈ᶜ-wkʳ (λ u → u) (LLq n η) (o₋ B)) e′ q (G₋ B) G₁
  gr : η ≺ᴵ lvG G₁
  gr = ≺ᴵ-respˡ (eη B) (grr (h₋ B))
  brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQq n C′ b′
  brN {b′} h {k′} e {D} d G′ = go gr (≺ᴵ-respʳ h e₁)
    where
    dC : D ≈ᶜ C
    dC = ≈ᶜ-trans d o
    o₁ : D₁ ≈ᶜ D
    o₁ = ≈ᶜ-wkˡ (λ u → u) (LLq n η) (≈ᶜ-sym dC)
    go : η ≺ᴵ lvG G₁ → b′ ≺ᴵ lvG G₁ → suc b′ ⊑ᴵ lvG G′
    go (via ex qx) h′@(via eb qb) with <ᴵ-dec qb qx
    ... | injᵃ s = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) e dC G′
    ... | injᵇ s = rdq o₁ G₁ h′ (Ω↓via (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym (≅ᴵ-trans e eb))))) G′
    ... | injᶜ c = rdq o₁ G₁ h′ (R→⊑ᵀ (R-ι↓ (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb)))) (RΩ̇ n (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb))))))) G′

BrCast : ∀ {n η η′ ψ ρ ψ′ ρ′} {C : Cx (suc n) zero ψ ρ} {C′ : Cx (suc n) zero ψ′ ρ′} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → Brq n η C → Brq n η′ C′
BrCast eq x′ o B = br-mk x′ (λ h e d → br B (≺ᴵ-respʳ h (≅ᴵ-sym eq)) e (≈ᶜ-trans d o)) (η₋ B) (D₋ B) (≈ᶜ-trans (o₋ B) (≈ᶜ-sym o)) (G₋ B)
                         (≅ᴵ-trans (≅ᴵ-sym eq) (eη B)) (≺ᴵ-respʳ (h₋ B) eq)
```

## §2 下移读出闭包守卫

```agda
record RT {n k φ χ} (E : Cx n k φ χ) : Set where
  constructor rtm
  field
    kr  : Ordᴵ
    Er  : Cx (suc n) zero φ (upd χ n (flo kr))
    ekr : kr ≅ᴵ k
open RT

rt : ∀ {n k φ χ} (E : Cx n k φ χ) → Dd E → RT E
rt (pD {k = k} C) d = rtm k C (≅ᴵ-refl k)
rt (ptr e C) d = rtm (kr (rt C d)) (Er (rt C d)) (≅ᴵ-trans (ekr (rt C d)) (≅ᴵ-sym e))
rt (ptr⁻ e C) d = rtm (kr (rt C d)) (Er (rt C d)) (≅ᴵ-trans (ekr (rt C d)) e)

rt-≈ : ∀ {n k φ χ ψ ρ} {E : Cx n k φ χ} {X : Cx n k ψ ρ} → E ≈ᶜ X → (dE : Dd E) (dX : Dd X) → Er (rt E dE) ≈ᶜ Er (rt X dX)
rt-≈ (pD o) dE dX = o
rt-≈ (ptr o) dE dX = rt-≈ o dE dX
rt-≈ (ptr⁻ o) dE dX = rt-≈ o dE dX

rtD : ∀ {n k ℓ φ χ ψ₀ ρ₀} (r : k ◃₁ ℓ) (X : Cx n ℓ φ χ) (d : Dd X) {C₀ : Cx (suc n) zero ψ₀ ρ₀} → Er (rt X d) ≈ᶜ C₀ → Σ (Dd (shD r X d)) λ d′ → Er (rt (shD r X d) d′) ≈ᶜ C₀
rtD r (pD C) d o = tt , ≈ᶜ-wkˡ (λ e → e) _ o
rtD zero (ptr (s≅ e) C) d o = rtD zero C d o
rtD (self i) (ptr (l≅ h) C) d o = rtD (self i) C d o
rtD zero (ptr⁻ (s≅ e) C) d o = rtD zero C d o
rtD (self i) (ptr⁻ (l≅ h) C) d o = rtD (self i) C d o

rtE : ∀ {n k ℓ φ χ ψ₀ ρ₀} (r : k ◃₁ ℓ) (X : Cx n ℓ φ χ) (d : Dd X) (u : Nd X ⊎ Dd X) {C₀ : Cx (suc n) zero ψ₀ ρ₀} → Er (rt X d) ≈ᶜ C₀ → Σ (Dd (shE r X u)) λ d′ → Er (rt (shE r X u) d′) ≈ᶜ C₀
rtE r X d (inj₁ n) o = ⊥-elim (Nd∧Dd X n d)
rtE r X d (inj₂ d₁) o = rtD r X d₁ (≈ᶜ-trans (rt-≈ (≈ᶜ-reflˡ′ X d₁ d o) d₁ d) o)
  where
  ≈ᶜ-reflˡ′ : ∀ {n ℓ φ χ ψ₀ ρ₀} (X : Cx n ℓ φ χ) (d₁ d : Dd X) {C₀ : Cx (suc n) zero ψ₀ ρ₀} → Er (rt X d) ≈ᶜ C₀ → X ≈ᶜ X
  ≈ᶜ-reflˡ′ (pD C) d₁ d o = pD (≈ᶜ-reflˡ o)
  ≈ᶜ-reflˡ′ (ptr e C) d₁ d o = ptr (≈ᶜ-reflˡ′ C d₁ d o)
  ≈ᶜ-reflˡ′ (ptr⁻ e C) d₁ d o = ptr⁻ (≈ᶜ-reflˡ′ C d₁ d o)

InvD : ∀ {n k b φ χ ψ₀ ρ₀ s} {X : Cx n k φ χ} {E : Cx n b Fl (κ Fl)} {C₀ : Cx (suc n) zero ψ₀ ρ₀} (d : Dd X) → Er (rt X d) ≈ᶜ C₀ → Sft X s E → Σ (Dd E) λ dE → Er (rt E dE) ≈ᶜ C₀
InvD d o (sB e) = Dd-≈ e d , ≈ᶜ-trans (rt-≈ e (Dd-≈ e d) d) o
InvD {X = X} d o (sS h) = let P = rtE zero X d (dh X) o in InvD (proj₁ P) (proj₂ P) h
InvD {X = X} d o (sL i h) = let P = rtE (self i) X d (dh X) o in InvD (proj₁ P) (proj₂ P) h
InvD {X = X} d o (sT e h) = InvD {X = ptr e X} d o h
InvD {X = X} d o (sT⁻ e h) = InvD {X = ptr⁻ e X} d o h

rt-val : ∀ {n k ψ₀ ρ₀} (E : Cx n k Fl (κ Fl)) (d : Dd E) {C₀ : Cx (suc n) zero ψ₀ ρ₀} → Er (rt E d) ≈ᶜ C₀ → {y : Q n k Fl (κ Fl)} → RΩv n k y → runᶜ E y ≅ˢ runᶜ (Er (rt E d)) (ι↓ {α = zero} (Ω̇ n (kr (rt E d))))
rt-val (pD C) d o hy = hy (pD (≈ᶜ-reflˡ o))
rt-val (ptr e C) d o hy = rt-val C d o (RΩv-tr e hy)
rt-val (ptr⁻ e C) d o hy = rt-val C d o (RΩv-tr⁻ e hy)

brVis : ∀ {n η ψ ρ} {C₀ : Cx (suc n) zero ψ ρ} {Y : CD n η} → Ctxᶜ Y → Y ≈ᶜ C₀ → (∀ {b} → b ≺ᴵ η → CQq n C₀ b) → VisQ η (pD Y)
brVis {n} {η} x o br₁ = visQ x (λ {b} {E} h G →
  let P = InvD tt o h
      dE = proj₁ P
      oE = proj₂ P
      R₁ = rt E dE
  in pull (rt-val E dE oE RΩv-Ω) (λ H → br₁ (Sft-lvT h) (ekr R₁) oE H) G)
```

## §3 $\dot\Omega$ 全体

```agda
zcOf : ∀ w (A : Set₁) → (w ≡ g₂ → A) → Zc w A
zcOf g₀ A f = tt₁
zcOf g₁ A f = tt₁
zcOf g₂ A f = f refl

KQ-sh : ∀ w {m k φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {C : Cx m (suc k) ψ ρ} → KQ w (suc k) C → KlT w k (sh zero (wkC le lc C))
KQ-sh g₀ {C = C} c = Ctx-sh zero _ (Ctx-wkC C c)
KQ-sh g₁ {le = le} {lc = lc} {C = C} v = Vis-shq (VisQ-≈ (Ctx-wkC C (cxQ v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl C (cxQ v))) v)
KQ-sh g₂ {le = le} {lc = lc} {C = C} v = Vis-shq (VisQ-≈ (Ctx-wkC C (cxQ v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl C (cxQ v))) v)

Vis-above : ∀ {m k ξ ζ ψ ρ} {D : Cx m k ξ ζ} {C′ : Cx m (suc k) ψ ρ} (E₀ : Cx m k Fl (κ Fl)) → E₀ ≈ᶜ D → VisQT k D → AboveΩ C′ D → (∀ {L} → Ev L ψ → Ev L Fl) → Sub m ρ (κ Fl) → VisQ (suc k) C′
Vis-above {m} {k} {C′ = C′} E₀ o₀ v a le lc = visQ (cxΩ a) (λ {b} {E} h G →
  let L₁ = Sft-lift (ctxᶜ-refl C′ (cxΩ a)) le lc h (Ω̇ m b) (RΩ̇ m (≅ᴵ-refl b))
      Wp = wrapΩ a (proj₁ L₁) (proj₁ (proj₂ L₁))
      u = proj₁ Wp
      fu = proj₁ (proj₂ (proj₂ Wp))
      d = ≅ˢ-trans (proj₂ (proj₂ L₁)) (proj₂ (proj₂ (proj₂ Wp)))
      S = stp (Sft-lvT h)
  in pull d (λ H →
       let J = fu (RΩ̇ m (≅ᴵ-refl k)) (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl k))) o₀ H
       in ⊑ᴵ-trans S (⊑ᴵ-trans (tpQ v (sB o₀) (proj₁ J)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ J)) (forceᴺ-HS _ H) (proj₂ J)))) G)
  where
  stp : ∀ {b} → b ≺ᴵ suc k → suc b ⊑ᴵ suc k
  stp (via e q) = s⊑ e q

KQ-St : ∀ w {m k ξ ζ} {C : Cx m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)} {C′ : Cx m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)} {le : ∀ {L} → Ev L (ξ ⊔ Fl) → Ev L ξ} {lc : Sub m (lo m ζ ∪ κ Fl) ζ} →
        KQ w (suc k) C → AboveΩ C′ (sh zero (wkC le lc C)) → KQ w (suc k) C′
KQ-St g₀ c a = cxΩ a
KQ-St g₁ {m} {C = C} {le = le} {lc = lc} v a =
  Vis-above (sh zero (wkC proj₂ (λ i q → proj₂) C)) (sh-≈ zero (wk≈ proj₂ (λ i q → proj₂) le lc (ctxᶜ-refl C (cxQ v)))) (KQ-sh g₂ v) a proj₂ (λ i q → proj₂)
KQ-St g₂ {m} {C = C} {le = le} {lc = lc} v a =
  Vis-above (sh zero (wkC proj₂ (λ i q → proj₂) C)) (sh-≈ zero (wk≈ proj₂ (λ i q → proj₂) le lc (ctxᶜ-refl C (cxQ v)))) (KQ-sh g₂ v) a proj₂ (λ i q → proj₂)

KQ-ι : ∀ w {m f s φ χ} i {C : Cx m (lim f s) φ χ} → KQ w (lim f s) C → Nd C → KQ w (f i) (pι (self i) C)
KQ-ι g₀ i c n = n , c
KQ-ι g₁ i {C} v n = VisQ-≈ (n , cxQ v) (shE-≈ (self i) (ctxᶜ-refl C (cxQ v)) (inj₁ n) (dh C)) (Vis-shl i v)
KQ-ι g₂ i {C} v n = VisQ-≈ (n , cxQ v) (shE-≈ (self i) (ctxᶜ-refl C (cxQ v)) (inj₁ n) (dh C)) (Vis-shl i v)

-- `omk` 的值是 sh 下的值 (不要求 R)
sh≡D : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (d : Dd C) (z : Q m k φ χ) (x : Q m ℓ φ χ) → runᶜ (shD r C d) z ≡ runᶜ C (omk r (intoU (◃₁→◃ r) z) x)
sh≡D {m = n} zero (pD C) d z x = run-wkC (λ e → e) (⇑ (upd-map n (λ i e → e) (tighten zero))) C (ι↓ z)
sh≡D {m = n} (self i) (pD C) d z x = run-wkC (λ e → e) (⇑ (upd-map n (λ i₁ e → e) (tighten (self i)))) C (ι↓ z)
sh≡D zero (ptr (s≅ e) C) d z x = sh≡D zero C d (trQ e z) (trQ (s≅ e) x)
sh≡D (self i) (ptr (l≅ h) C) d z x = sh≡D (self i) C d (trQ (h i) z) (trQ (l≅ h) x)
sh≡D zero (ptr⁻ (s≅ e) C) d z x = sh≡D zero C d (tr⁻Q e z) (tr⁻Q (s≅ e) x)
sh≡D (self i) (ptr⁻ (l≅ h) C) d z x = sh≡D (self i) C d (tr⁻Q (h i) z) (tr⁻Q (l≅ h) x)

sh≡E : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (u : Nd C ⊎ Dd C) (z : Q m k φ χ) → runᶜ (shE r C u) z ≡ runᶜ C (Up r z)
sh≡E zero C (inj₁ n) z = sym (nd-omk zero C n z (ι zero z))
sh≡E (self i) C (inj₁ n) z = sym (nd-omk (self i) C n z (ι (self i) z))
sh≡E zero C (inj₂ d) z = sh≡D zero C d z (ι zero z)
sh≡E (self i) C (inj₂ d) z = sh≡D (self i) C d z (ι (self i) z)

Up-congᵗ : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {z : Q m k φ χ} {z′ : Q m k ψ ρ} → z ⊑ᵗ z′ → Up r z ⊑ᵗ Up r z′
Up-congᵗ r {z} {z′} h {C} {C′} o G G′ =
  ⊑-trans (proj₂ (proj₂ J)) (⊑-trans (h (sh-≈ r o) (proj₁ J) (proj₁ K)) (proj₁ (proj₂ K)))
  where
  J = pull≅ (sh≡E r C (dh C) z) G
  K = pull≅ (sh≡E r C′ (dh C′) z′) G′

Ω̇G′ : ∀ w → inp w ≡ w → ∀ m k → Gq w m k (KQ w k) (Ω̇ m k)
Ω̇G′ w iw zero zero = Gmono (KQ→Ctx w) Ω̇G₀
Ω̇G′ w iw (suc n) zero =
  Gmono (KQ→Ctx w)
    (gcl 𝓥 (λ c → c) (λ η C → Brq n η C) BrCast
       (gw (λ E → 𝓥 E × VisQ (suc zero) (pD E))
           (λ {C} c → Ctx-wkC C c , brVis (Ctx-wkC C c) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C c)) (λ { (via z≅ zero) → brZ c ; (via e (suc ())) }))
           (ID proj₂ proj₁ (Ω̇G′ g₂ refl n (suc zero))))
       (λ η → gw (λ E → 𝓥 E × VisQ η (pD E))
           (λ {C} B → Ctx-wkC C (cxB B) , brVis (Ctx-wkC C (cxB B)) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C (cxB B))) (br B))
           (ID proj₂ proj₁ (Ω̇G′ g₂ refl n η)))
       (rwk (R-ι↓ (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _))))
       (λ η η′ d → rwk (R-ι↓ d (RΩ̇ n d)))
       (λ η h → wk-lᵗ (wk-rᵗ (Ωm↓ h)))
       (λ η η′ h u → wk-lᵗ (wk-rᵗ (Ωm↓ u)))
       (λ c G ())
       (λ η c G ())
       (ch₀q _)
       chSq)
Ω̇G′ w iw m (suc k) =
  gΩ (λ ξ ζ → KQ w (suc k))
     (λ ξ ζ c x o → KQ-≈ w x o c)
     (λ ξ ζ D → sh zero (wkC proj₁ (Lζ ζ) D))
     (λ ξ ζ {C} c u ru → subst (λ v → runᶜ (sh zero (wkC proj₁ (Lζ ζ) C)) u ≅ˢ v) (run-wkC proj₁ (Lζ ζ) C (Up zero u))
         (up-run zero (ctxᶜ-refl (wkC proj₁ (Lζ ζ) C) (Ctx-wkC C (KQ→Ctx w c))) ru))
     (λ 𝓔 inc″ ξ ζ z rz₁ gz → Hb 𝓔 inc″ ξ ζ z rz₁ (subst (λ g → Gq g m k ((λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ) z) iw gz))
     (λ ξ ζ c → KQ-sh w c)
     (λ ξ ζ c a _ → KQ-St w c a)
     (λ ξ ξ′ ζ ζ′ x o c → KQ-≈ w x o c)
     (λ u → wk-lᵗ (wk-rᵗ (Up-congᵗ zero u)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-Up zero l))
  where
  Lζ : ∀ ζ → Sub m (lo m ζ ∪ κ Fl) ζ
  Lζ ζ i q e = subst (Ev _) (lo-lt ζ q) (proj₁ e)
  Hb : (𝓔 : ∀ ξ ζ → ClT m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → KQ w (suc k) C) → ∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z →
       Gq w m k ((λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ) z → Gq w m (suc k) (𝓔 ξ ζ) (qwk proj₁ (Lζ ζ) (omk zero z (ι zero z)))
  Hb 𝓔 inc″ ξ ζ z rz₁ gz =
    gw 𝓖₁ (λ {D} c₁ → Ctx-wkC D (KQ→Ctx w (inc″ ξ ζ c₁)) , D , c₁ , ctxᶜ-refl (wkC proj₁ (Lζ ζ) D) (Ctx-wkC D (KQ→Ctx w (inc″ ξ ζ c₁))))
      (gm {r = zero} {z = z}
         (zcOf w _ (λ { refl → λ 𝓔′ inc → Gmono (λ { (x , C , c , d , o) →
              let P = inc c in x , proj₁ (proj₂ P) , proj₁ (proj₂ (proj₂ P)) , ≈ᶜ-trans o (shE-≈ zero (proj₂ (proj₂ (proj₂ P))) (inj₂ d) (dh _)) }) gz }))
         rz₁
         (Iota zero {𝓖 = λ C → 𝓖₁ C × Nd C} {𝓧 = (λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ}
            (λ { ((x , D , c₁ , o) , n) → (n , x) , D , c₁ , shE-≈ zero o (inj₁ n) (dh _) })
            (λ { ((x , _) , n) → x , n })
            gz))
    where
    𝓖₁ : ClT m (suc k) ξ ζ
    𝓖₁ E = Ctxᶜ E × (Σ _ λ D → 𝓔 ξ ζ D × (E ≈ᶜ wkC proj₁ (Lζ ζ) D))
Ω̇G′ w iw m (lim f s) =
  gl (λ i → gm {r = self i} {z = Ω̇ m (f i)}
        (zcOf w _ (λ { refl → λ 𝓔′ inc → Gmono (λ { (x , C , c , d , o) →
             VisQ-≈ x (≈ᶜ-trans o (shE-≈ (self i) (ctxᶜ-refl C (cxQ (inc c))) (inj₂ d) (dh C))) (Vis-shl i (inc c)) }) (Ω̇G′ g₂ refl m (f i)) }))
        (RΩ̇ m (≅ᴵ-refl (f i)))
        (Iota (self i) {𝓖 = λ C → KQ w (lim f s) C × Nd C} {𝓧 = KQ w (f i)} (λ { (c , n) → KQ-ι w i c n }) (λ { (c , n) → KQ→Ctx w c , n }) (Ω̇G′ w iw m (f i))))
     (λ i → Up≤ i (suc i) (s i))

Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)
Ω̇G g m k = Ω̇G′ (inp g) (inp-idem g) m k
```
