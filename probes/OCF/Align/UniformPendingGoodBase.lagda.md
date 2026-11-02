# 统一折叠上的三层遗传好树 (一): 定义、搬运与加法

> 接 [UniformNFBase](UniformNFBase.lagda.md) 与 [PendingBase](PendingBase.lagda.md). 本文把 PendingBase §1–§4 移到统一折叠, 对任意前缀 $P$ 参数化: `Cvd`、`ColC`、`CovΛ` 都相对 $P$. 除这个参数外, 定义与证明逐字相同.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPendingGoodBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS)
open Restrˢ
open import OCF.Align.UniformS using (⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; force-≅; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-reflˡ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ;
  ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg)
open import OCF.Align.Uniform2Base using (Run; _≈ᴿ_)
open import OCF.Align.UniformNFBase using (_⊑ᵒ_; add-cong; tr-cong; tr⁻-cong; up-l; up-r; Ω-monoᵒ; rule4ᵒ; FlΛ; FlΛ-add;
  CovΛ; ColC; ColC-tr; ColC-tr⁻; dom-cov; idO; col)
open import OCF.Align.UniformNFDepth0 using (NZ)
```

## §1 记号无关的辅助

```agda

back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (resˢ q e))} → u ⊑ᵒ u′ → backˢ (resˢ q e) u ⊑ᵒ backˢ (resˢ q e) u′
back-mono zero      (s≅ e) h = tr⁻-cong h
back-mono (suc q)   (s≅ e) h = back-mono q e h
back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (res⁻ˢ q e))} → u ⊑ᵒ u′ → backˢ (res⁻ˢ q e) u ⊑ᵒ backˢ (res⁻ˢ q e) u′
back⁻-mono zero      (s≅ e) h = tr-cong h
back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → backˢ (resˢ q e) u ≅ˢ backˢ (resˢ q e) u
self-back q e d = ≅ˢ-reflˡ (backˢ-≅ q e d)

self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → backˢ (res⁻ˢ q e) u ≅ˢ backˢ (res⁻ˢ q e) u
self-back⁻ q e d = ≅ˢ-reflˡ (back⁻ˢ-≅ q e d)

data Mode : Set where
  mC mP mV : Mode

module GoodP {fl} (P : Run fl) (rP : P ≈ᴿ P) where

  Cvd : Ordᴵ → Ordᴵ → Set
  Cvd K c = Σ Ordᴵ λ φ → CovΛ P φ c × φ ⊑ᴵ K

  VisD : ∀ {ℓ} → Mode → (c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
  VisD mC c t₀ g = ⊤
  VisD mP c t₀ g = ⊤
  VisD mV c t₀ g = ColC P c t₀ × (∀ η e → ColC P c (g η e))

  Dom : Mode → Ordᴵ → (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
  Dom m K zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                             (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
  Dom m K (suc _)   c t₀ g = Cvd K c × VisD m c t₀ g
  Dom m K (lim _ _) c t₀ g = Cvd K c × VisD m c t₀ g

  module _ (ℓ : Ordᴵ) (G< : Mode → Ordᴵ → (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
    data Good₊ : Mode → Ordᴵ → Ordˢ ℓ → Set where
      bz : ∀ {m K} → Good₊ m K Ord₊ˢ.zero
      bs : ∀ {m K a} → Good₊ m K a → Good₊ m K (Ord₊ˢ.suc a)
      bl : ∀ {m K} {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ m K (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ m K (Ord₊ˢ.lim h)
      biH : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} →
            (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mC a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mC a (f (intoˢ (<→◃ p) z))) →
            (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
            Good₊ mC K (Ord₊ˢ.limᵢ p f)
      biL : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K →
            (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mC a (f (intoˢ (<→◃ p) z))) →
            (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
            Good₊ mC K (Ord₊ˢ.limᵢ p f)
      biP : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K →
            (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mP a (f (intoˢ (<→◃ p) z))) →
            (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
            Good₊ mP K (Ord₊ˢ.limᵢ p f)
      biV : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K → (κ : Ordᴵ) → j ⊑ᴵ κ → κ ⊑ᴵ K →
            (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mP a (f (intoˢ (<→◃ p) z))) →
            (∀ (z : Ordˢ j) → z ≅ˢ z → G< mP κ j (<→◃ p) (intoˢ (<→◃ p) z) → (κ ⊑ᴵ j → G< mV κ j (<→◃ p) (intoˢ (<→◃ p) z)) →
               Good₊ mV κ (f (intoˢ (<→◃ p) z))) →
            (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
            Good₊ mV K (Ord₊ˢ.limᵢ p f)
      bu : ∀ {m K k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< m K k (◃₁→◃ r) x → Good₊ m K (Ord₊ˢ.up r x)
      bŝ : ∀ {m K c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
           Good₊ m K t₀ → (∀ η e → Good₊ m K (g η e)) →
           t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
           (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
           Dom m K ℓ c t₀ g → Good₊ m K (Ord₊ˢ.ŝ c t₀ g)
      bĉ : ∀ {m K c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
           (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
           c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
           (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
           (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
           (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
           Good₊ m K o₀ → (∀ η e → Good₊ m K (o η e)) →
           (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
           Good₊ m K (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

  Gd : ∀ {ℓ} → Mode → Ordᴵ → (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
  Gd m K i zero         x = Good₊ i Gd m K x
  Gd m K i (suc r)      x = Gd m K i r x
  Gd m K _ (self {f} n) x = Good₊ (f n) Gd m K x
  Gd m K i (lim n r)    x = Gd m K i r x

  Good : ∀ {ℓ} → Mode → Ordᴵ → Ordˢ ℓ → Set
  Good {ℓ} = Good₊ ℓ Gd

  Gd→Good : ∀ {i ℓ m K} (r : i ◃ ℓ) {x : Ordˢ i} → Gd m K i r (intoˢ r x) → Good m K x
  Gd→Good zero      g = g
  Gd→Good (suc r)   g = Gd→Good r g
  Gd→Good (self n)  g = g
  Gd→Good (lim n r) g = Gd→Good r g

  Good→Gd : ∀ {i ℓ m K} (r : i ◃ ℓ) {x : Ordˢ i} → Good m K x → Gd m K i r (intoˢ r x)
  Good→Gd zero      g = g
  Good→Gd (suc r)   g = Good→Gd r g
  Good→Gd (self n)  g = g
  Good→Gd (lim n r) g = Good→Gd r g

  Gd-conv : ∀ {i ℓ ℓ′ m K} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd m K i r (intoˢ r x) → Gd m K i r′ (intoˢ r′ x)
  Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

  Good→Goodᶻ : ∀ {m K} {x : Ordˢ zero} → Good m K x → Goodᶻ (toZ x)
  Good→Goodᶻ bz         = Goodᶻ.gz
  Good→Goodᶻ (bs g)     = Goodᶻ.gs (Good→Goodᶻ g)
  Good→Goodᶻ (bl hg st) = Goodᶻ.gl (λ n → Good→Goodᶻ (hg n)) (λ n → st n idO (Good→Goodᶻ (hg n)) (Good→Goodᶻ (hg (suc n))))
  Good→Goodᶻ (biH {p = ()} hb hm)
  Good→Goodᶻ (biL {p = ()} j hb hm)
  Good→Goodᶻ (biP {p = ()} j hb hm)
  Good→Goodᶻ (biV {p = ()} j κ jκ κK tr ab hm)
  Good→Goodᶻ (bu {r = ()} g)
  Good→Goodᶻ (bŝ g₀ gg et eg m mm (d₀ , dE)) =
    Goodᶻ.gc G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
             (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
             G₀ Gg (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
    where
    G₀ = Good→Goodᶻ g₀
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good→Goodᶻ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    Goodᶻ.gc G₀ Gg d₀ dE m₀ mE (Good→Goodᶻ go) (λ η e → Good→Goodᶻ (gO η e))
             (λ η e → mo η e idO (Good→Goodᶻ go) (Good→Goodᶻ (gO η e)))
             (λ η e η′ e′ h → mO η e η′ e′ h idO (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))

  Dom-mono : ∀ {m K K′} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → K ⊑ᴵ K′ → Dom m K ℓ c t₀ g → Dom m K′ ℓ c t₀ g
  Dom-mono zero      h d = d
  Dom-mono (suc _)   h ((φ , cv , φK) , v) = (φ , cv , ⊑ᴵ-trans φK h) , v
  Dom-mono (lim _ _) h ((φ , cv , φK) , v) = (φ , cv , ⊑ᴵ-trans φK h) , v

  Good-mono : ∀ {ℓ m K K′} {x : Ordˢ ℓ} → K ⊑ᴵ K′ → Good m K x → Good m K′ x
  Good-mono h bz         = bz
  Good-mono h (bs g)     = bs (Good-mono h g)
  Good-mono h (bl hg st) = bl (λ n → Good-mono h (hg n)) st
  Good-mono h (biH hb hm) = biH (λ a k → hb a (⊑ᴵ-trans h k)) hm
  Good-mono h (biL j hb hm) = biL (⊑ᴵ-trans j h) (λ a k → hb a (⊑ᴵ-trans h k)) hm
  Good-mono h (biP j hb hm) = biP (⊑ᴵ-trans j h) (λ a k → hb a (⊑ᴵ-trans h k)) hm
  Good-mono h (biV j κ jκ κK tr ab hm) = biV (⊑ᴵ-trans j h) κ jκ (⊑ᴵ-trans κK h) (λ a k → tr a (⊑ᴵ-trans h k)) ab hm
  Good-mono h (bu {r = zero} g)   = bu {r = zero} (Good-mono h g)
  Good-mono h (bu {r = self n} g) = bu {r = self n} (Good-mono h g)
  Good-mono {ℓ} h (bŝ g0 gg et eg m mm dm) = bŝ (Good-mono h g0) (λ η e → Good-mono h (gg η e)) et eg m mm (Dom-mono ℓ h dm)
  Good-mono h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-mono h go) (λ η e → Good-mono h (gO η e)) mo mO

  Dom-V→P : ∀ {K} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → Dom mV K ℓ c t₀ g → Dom mP K ℓ c t₀ g
  Dom-V→P zero      d = d
  Dom-V→P (suc _)   (cv , _) = cv , tt
  Dom-V→P (lim _ _) (cv , _) = cv , tt

  Dom-P→C : ∀ {K} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → Dom mP K ℓ c t₀ g → Dom mC K ℓ c t₀ g
  Dom-P→C zero      d = d
  Dom-P→C (suc _)   (cv , _) = cv , tt
  Dom-P→C (lim _ _) (cv , _) = cv , tt

  V→P : ∀ {ℓ K} {x : Ordˢ ℓ} → Good mV K x → Good mP K x
  V→P bz         = bz
  V→P (bs g)     = bs (V→P g)
  V→P (bl hg st) = bl (λ n → V→P (hg n)) st
  V→P (biV j κ jκ κK tr ab hm) = biP j tr hm
  V→P (bu {r = zero} g)   = bu {r = zero} (V→P g)
  V→P (bu {r = self n} g) = bu {r = self n} (V→P g)
  V→P {ℓ} (bŝ g0 gg et eg m mm dm) = bŝ (V→P g0) (λ η e → V→P (gg η e)) et eg m mm (Dom-V→P ℓ dm)
  V→P (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) = bĉ G₀ Gg d₀ dE m₀ mE (V→P go) (λ η e → V→P (gO η e)) mo mO

  P→C : ∀ {ℓ K} {x : Ordˢ ℓ} → Good mP K x → Good mC K x
  P→C bz         = bz
  P→C (bs g)     = bs (P→C g)
  P→C (bl hg st) = bl (λ n → P→C (hg n)) st
  P→C (biP j tr hm) = biL j (λ a h z ez g → P→C (tr a h z ez g)) hm
  P→C (bu {r = zero} g)   = bu {r = zero} (P→C g)
  P→C (bu {r = self n} g) = bu {r = self n} (P→C g)
  P→C {ℓ} (bŝ g0 gg et eg m mm dm) = bŝ (P→C g0) (λ η e → P→C (gg η e)) et eg m mm (Dom-P→C ℓ dm)
  P→C (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) = bĉ G₀ Gg d₀ dE m₀ mE (P→C go) (λ η e → P→C (gO η e)) mo mO

  Good-Ωᶜ : ∀ a K → Good mC K (Ωˢ a)
  Good-Ωᶜ zero      K = bs bz
  Good-Ωᶜ (suc c)   K = biH (λ a h z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
  Good-Ωᶜ (lim g s) K = bl (λ n → bu (Good-Ωᶜ (g n) K)) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

  Good-Ωᴾ : ∀ a {K} → a ⊑ᴵ K → Good mP K (Ωˢ a)
  Good-Ωᴾ zero      h = bs bz
  Good-Ωᴾ (suc c)   h = biP (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) h) (λ a k z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
  Good-Ωᴾ (lim g s) h = bl (λ n → bu (Good-Ωᴾ (g n) (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) h))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

  Good-Ωⱽ : ∀ a {K} → a ⊑ᴵ K → Good mV K (Ωˢ a)
  Good-Ωⱽ zero      h = bs bz
  Good-Ωⱽ (suc c)   h = biV cK c ⊑ᴵ-refl cK (λ a k z ez g → bu g) (λ z ez gp gv → bu (gv ⊑ᴵ-refl)) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
    where cK = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) h
  Good-Ωⱽ (lim g s) h = bl (λ n → bu (Good-Ωⱽ (g n) (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) h))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

  Dom0-≅ : ∀ {m m′ K K′ c} {t₀ t₀′ : Ordˢ zero} {g g′ : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} →
           Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀′ ≅ˢ t₀ → (∀ η d → g′ η d ≅ˢ g η d) →
           Dom m′ K′ zero c t₀ g → Dom m′ K′ zero c t₀′ g′
  Dom0-≅ g0 gg et eg (d₀ , dE) =
    (λ G → ⊑ᴵ-≅ʳ (d₀ (Good→Goodᶻ g0)) (toLevel-≅ (force-HS _ (Good→Goodᶻ g0)) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym et)) (Good→Goodᶻ g0) G))) ,
    (λ η d G → ⊑ᴵ-≅ʳ (dE η d (Good→Goodᶻ (gg η d))) (toLevel-≅ (force-HS _ (Good→Goodᶻ (gg η d))) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym (eg η d))) (Good→Goodᶻ (gg η d)) G)))

  VisD-tr : ∀ m {c a b} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
            VisD m c t₀ g → VisD m c (trˢ e t₀) (λ η d → trˢ e (g η d))
  VisD-tr mC e v = tt
  VisD-tr mP e v = tt
  VisD-tr mV e (c₀ , cg) = ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

  VisD-tr⁻ : ∀ m {c a b} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
             VisD m c t₀ g → VisD m c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  VisD-tr⁻ mC e v = tt
  VisD-tr⁻ mP e v = tt
  VisD-tr⁻ mV e (c₀ , cg) = ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)

  Dom-tr : ∀ {m K a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
           Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
           Dom m K a c t₀ g → Dom m K b c (trˢ e t₀) (λ η d → trˢ e (g η d))
  Dom-tr {m} {K} z≅ g0 gg et eg h = Dom0-≅ {m′ = m} {K′ = K} g0 gg (trˢ-≅ z≅ et) (λ η d → trˢ-≅ z≅ (eg η d)) h
  Dom-tr {m} e@(s≅ _) g0 gg et eg (cv , v) = cv , VisD-tr m e v
  Dom-tr {m} e@(l≅ _) g0 gg et eg (cv , v) = cv , VisD-tr m e v

  Dom-tr⁻ : ∀ {m K a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
            Dom m K b c t₀ g → Dom m K a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Dom-tr⁻ {m} {K} z≅ g0 gg et eg h = Dom0-≅ {m′ = m} {K′ = K} g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
  Dom-tr⁻ {m} e@(s≅ _) g0 gg et eg (cv , v) = cv , VisD-tr⁻ m e v
  Dom-tr⁻ {m} e@(l≅ _) g0 gg et eg (cv , v) = cv , VisD-tr⁻ m e v

  Good-tr    : ∀ {m K a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Good m K x → Good m K (trˢ e x)
  Good-tr⁻   : ∀ {m K a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Good m K x → Good m K (tr⁻ˢ e x)
  Good-back  : ∀ {m K j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Good m K u → Good m K (backˢ (resˢ q e) u)
  Good-back⁻ : ∀ {m K j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Good m K u → Good m K (backˢ (res⁻ˢ q e) u)

  subT : ∀ {m K j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ a) (z : Ordˢ (repˢ (resˢ q e))) →
         Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) z)))) →
         Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z))))))
  subT {m} {K} q e f z g = subst (λ w → Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) g

  subT⁻ : ∀ {m K j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ b) (z : Ordˢ (repˢ (res⁻ˢ q e))) →
          Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) z)))) →
          Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))))))
  subT⁻ {m} {K} q e f z g = subst (λ w → Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) g

  monT : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ a) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
         ∀ {z z′ : Ordˢ (repˢ (resˢ q e))} → z ⊑ᵒ z′ →
         trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z))))) ⊑ᵒ
         trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z′)))))
  monT q e f hm {z} {z′} h = subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
                             (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′))
                             (tr-cong (hm (back-mono q e h)))

  monT⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ b) →
          (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
          ∀ {z z′ : Ordˢ (repˢ (res⁻ˢ q e))} → z ⊑ᵒ z′ →
          tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))))) ⊑ᵒ
          tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)))))
  monT⁻ q e f hm {z} {z′} h = subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
                              (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′))
                              (tr⁻-cong (hm (back⁻-mono q e h)))

  Good-tr e bz         = bz
  Good-tr e (bs g)     = bs (Good-tr e g)
  Good-tr e (bl hg st) = bl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
  Good-tr e (biH {p = q} {f = f} hb hm) = biH
    (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
  Good-tr e (biL {p = q} {f = f} j hb hm) = biL (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j)
    (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
  Good-tr e (biP {p = q} {f = f} j hb hm) = biP (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j)
    (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
  Good-tr e (biV {p = q} {f = f} j κ jκ κK tr ab hm) = biV (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j) κ (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) jκ) κK
    (λ a h z ez g → subT q e f z (Good-tr e (tr a h (backˢ (resˢ q e) z) (self-back q e ez)
                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))))
    (λ z ez gp gv → subT q e f z (Good-tr e (ab (backˢ (resˢ q e) z) (self-back q e ez)
                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) gp)))
                     (λ κj → Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) (gv (⊑ᴵ-≅ʳ κj (eqˢ (resˢ q e))))))))))
    (monT q e f hm)
  Good-tr (s≅ e) (bu {r = zero} g)   = bu (Good-tr e g)
  Good-tr (l≅ f) (bu {r = self n} g) = bu (Good-tr (f n) g)
  Good-tr e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr e g0) (λ η d → Good-tr e (gg η d)) (self-trˢ e et)
       (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
       (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
       (Dom-tr e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr e go) (λ η d → Good-tr e (gO η d))
       (λ η d → tr-cong (mo η d)) (λ η d η′ d′ h → tr-cong (mO η d η′ d′ h))

  Good-tr⁻ e bz         = bz
  Good-tr⁻ e (bs g)     = bs (Good-tr⁻ e g)
  Good-tr⁻ e (bl hg st) = bl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
  Good-tr⁻ e (biH {p = q} {f = f} hb hm) = biH
    (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                     (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
  Good-tr⁻ e (biL {p = q} {f = f} j hb hm) = biL (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j)
    (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                     (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
  Good-tr⁻ e (biP {p = q} {f = f} j hb hm) = biP (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j)
    (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                     (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
  Good-tr⁻ e (biV {p = q} {f = f} j κ jκ κK tr ab hm) = biV (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j) κ (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) jκ) κK
    (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (tr a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                     (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
    (λ z ez gp gv → subT⁻ q e f z (Good-tr⁻ e (ab (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                     (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) gp)))
                     (λ κj → Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) (gv (⊑ᴵ-≅ʳ κj (eqˢ (res⁻ˢ q e))))))))))
    (monT⁻ q e f hm)
  Good-tr⁻ (s≅ e) (bu {r = zero} g)   = bu (Good-tr⁻ e g)
  Good-tr⁻ (l≅ f) (bu {r = self n} g) = bu (Good-tr⁻ (f n) g)
  Good-tr⁻ e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr⁻ e g0) (λ η d → Good-tr⁻ e (gg η d)) (self-tr⁻ˢ e et)
       (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
       (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
       (Dom-tr⁻ e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr⁻ e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr⁻ e go) (λ η d → Good-tr⁻ e (gO η d))
       (λ η d → tr⁻-cong (mo η d)) (λ η d η′ d′ h → tr⁻-cong (mO η d η′ d′ h))

  Good-back zero      (s≅ e) g = Good-tr⁻ e g
  Good-back (suc q)   (s≅ e) g = Good-back q e g
  Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

  Good-back⁻ zero      (s≅ e) g = Good-tr e g
  Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
  Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g

  NV : Mode → Set
  NV mC = ⊤
  NV mP = ⊤
  NV mV = ⊥

  NV-vis : ∀ m {ℓ c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NV m → VisD m c t₀ g
  NV-vis mC nv = tt
  NV-vis mP nv = tt

  subA : ∀ {m K j k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) (z : Ordˢ j) →
         Good m K (addˢ a σ (f (intoˢ (<→◃ q) z))) →
         Good m K (addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z)))))
  subA {m} {K} {a = a} {σ = σ} q f z g = subst (λ u → Good m K (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z)) g

  monA : ∀ {j k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → a ≅ˢ a →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
         ∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ →
         addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z)))) ⊑ᵒ
         addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z′))))
  monA {a = a} {σ = σ} q f ea hm {z} {z′} h =
    subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
           (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h))

  Good-add : ∀ {m K k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → NV m → NZ ℓ → Good m K a → a ≅ˢ a → Good m K b → Good m K (addˢ a σ b)
  Good-add nv nz ga ea bz          = ga
  Good-add nv nz ga ea (bs g)      = bs (Good-add nv nz ga ea g)
  Good-add nv nz ga ea (bl hg st)  = bl (λ n → Good-add nv nz ga ea (hg n)) (λ n → add-cong refl ea (st n))
  Good-add {σ = σ} nv nz ga ea (biH {p = q} {f = f} hb hm) = biH
    (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (monA {σ = σ} q f ea hm)
  Good-add {σ = σ} nv nz ga ea (biL {p = q} {f = f} j hb hm) = biL j
    (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (monA {σ = σ} q f ea hm)
  Good-add {σ = σ} nv nz ga ea (biP {p = q} {f = f} j hb hm) = biP j
    (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (monA {σ = σ} q f ea hm)
  Good-add () nz ga ea (biV j κ jκ κK tr ab hm)
  Good-add nv nz ga ea (bu {r = zero} g)   = Good-add nv nz ga ea g
  Good-add nv nz ga ea (bu {r = self n} g) = Good-add nv nz ga ea g
  Good-add {k = zero} nv nz ga ea (bŝ g0 gg et eg m mm dm) =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good-add {k = suc _} {ℓ = zero} nv () ga ea (bŝ g0 gg et eg m mm dm)
  Good-add {m = md} {k = suc _} {ℓ = suc _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
    bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
  Good-add {m = md} {k = suc _} {ℓ = lim _ _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
    bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
  Good-add {k = lim _ _} {ℓ = zero} nv () ga ea (bŝ g0 gg et eg m mm dm)
  Good-add {m = md} {k = lim _ _} {ℓ = suc _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
    bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
  Good-add {m = md} {k = lim _ _} {ℓ = lim _ _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
    bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
  Good-add nv nz ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-add nv nz ga ea go) (λ η e → Good-add nv nz ga ea (gO η e))
       (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

  Good-add₀ : ∀ {m K K′} {a : Ordˢ zero} {σ : Simᴵ zero zero} {b : Ordˢ zero} → Good m K a → a ≅ˢ a → Good m K′ b → Good m K (addˢ a σ b)
  Good-add₀ ga ea bz          = ga
  Good-add₀ ga ea (bs g)      = bs (Good-add₀ ga ea g)
  Good-add₀ ga ea (bl hg st)  = bl (λ n → Good-add₀ ga ea (hg n)) (λ n → add-cong refl ea (st n))
  Good-add₀ ga ea (biH {p = ()} hb hm)
  Good-add₀ ga ea (biL {p = ()} j hb hm)
  Good-add₀ ga ea (biP {p = ()} j hb hm)
  Good-add₀ ga ea (biV {p = ()} j κ jκ κK tr ab hm)
  Good-add₀ ga ea (bu {r = ()} g)
  Good-add₀ ga ea (bŝ g0 gg et eg m mm dm) =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       (Good-add₀ ga ea g0) (λ η e → Good-add₀ ga ea (gg η e))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good-add₀ ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-add₀ ga ea go) (λ η e → Good-add₀ ga ea (gO η e))
       (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

  V-add : ∀ {K a₀ k ℓ} {c : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → NZ ℓ → Good mV a₀ c → (∀ {φ} → φ ⊑ᴵ a₀ → FlΛ φ c) → c ≅ˢ c →
          K ⊑ᴵ a₀ → Good mP K b → b ≅ˢ b → Good mV a₀ (addˢ c σ b)
  V-add nz gc fc ec h bz eb       = gc
  V-add nz gc fc ec h (bs g) eb   = bs (V-add nz gc fc ec h g (s-invˢ eb))
  V-add nz gc fc ec h (bl hg st) eb = bl (λ n → V-add nz gc fc ec h (hg n) (l-invˢ eb n)) (λ n → add-cong refl ec (st n))
  V-add {a₀ = a₀} {σ = σ} nz gc fc ec h (biP {p = q} {f = f} j tr hm) eb = biV (⊑ᴵ-trans j h) a₀ (⊑ᴵ-trans j h) ⊑ᴵ-refl
    (λ a k z ez g → subA {σ = σ} q f z (Good-add tt nz (Good-mono k (V→P gc)) ec (tr a (⊑ᴵ-trans h k) z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (λ z ez gp gv → subA {σ = σ} q f z (V-add nz gc fc ec ⊑ᴵ-refl (tr a₀ h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) gp)) (i-respˢ eb ez)))
    (monA {σ = σ} q f ec hm)
  V-add nz gc fc ec h (bu {r = zero} g) eb   = V-add nz gc fc ec h g (u-reflˢ zero eb)
  V-add nz gc fc ec h (bu {r = self n} g) eb = V-add nz gc fc ec h g (u-reflˢ (self n) eb)
  V-add {k = zero} nz gc fc ec h (bŝ g0 gg et eg m mm dm) eb =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h′ → mm η e η′ e′ h′ idO (Gg η e) (Gg η′ e′))
       (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  V-add {k = suc _} {ℓ = zero} () gc fc ec h (bŝ g0 gg et eg m mm dm) eb
  V-add {k = suc _} {ℓ = suc _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
    bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
       (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
       (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov rP (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov rP (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
  V-add {k = suc _} {ℓ = lim _ _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
    bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
       (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
       (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov rP (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov rP (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
  V-add {k = lim _ _} {ℓ = zero} () gc fc ec h (bŝ g0 gg et eg m mm dm) eb
  V-add {k = lim _ _} {ℓ = suc _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
    bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
       (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
       (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov rP (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov rP (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
  V-add {k = lim _ _} {ℓ = lim _ _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
    bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
       (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
       (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov rP (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov rP (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
  V-add nz gc fc ec h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) eb =
    bĉ G₀ Gg d₀ dE m₀ mE (V-add nz gc fc ec h go (ĉ-refl₀ eb)) (λ η e → V-add nz gc fc ec h (gO η e) (ĉ-reflg eb η e))
       (λ η e → add-cong refl ec (mo η e)) (λ η e η′ e′ h′ → add-cong refl ec (mO η e η′ e′ h′))

  Good-iter : ∀ {m K ℓ} {c : Ordˢ ℓ} → NV m → NZ ℓ → Good m K c → c ≅ˢ c → ∀ n → Good m K (iter (c +ˢ_) Ord₊ˢ.zero n)
  Good-iter nv nz gc ec zero    = bz
  Good-iter nv nz gc ec (suc n) = Good-add nv nz gc ec (Good-iter nv nz gc ec n)

  V-iter : ∀ {a₀ ℓ} {c : Ordˢ ℓ} → NZ ℓ → Good mV a₀ c → (∀ {φ} → φ ⊑ᴵ a₀ → FlΛ φ c) → c ≅ˢ c → ∀ n →
           Good mV a₀ (iter (c +ˢ_) Ord₊ˢ.zero n) × (iter (c +ˢ_) Ord₊ˢ.zero n ≅ˢ iter (c +ˢ_) Ord₊ˢ.zero n)
  V-iter nz gc fc ec zero    = bz , z≅
  V-iter nz gc fc ec (suc n) = V-add nz gc fc ec ⊑ᴵ-refl (V→P (proj₁ (V-iter nz gc fc ec n))) (proj₂ (V-iter nz gc fc ec n))
                             , addˢ-≅ refl ec (proj₂ (V-iter nz gc fc ec n))

  Good-iter₀ : ∀ {m K} {c : Ordˢ zero} → Good m K c → c ≅ˢ c → ∀ n → Good m K (iter (c +ˢ_) Ord₊ˢ.zero n)
  Good-iter₀ gc ec zero    = bz
  Good-iter₀ gc ec (suc n) = Good-add₀ gc ec (Good-iter₀ gc ec n)

```
