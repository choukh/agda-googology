# Uniform3 上的无符号闭包定理 (二): `Goodᴺ` 上的观测前序

> [UniformPendingNBase](UniformPendingNBase.lagda.md) 的重编译. 改动: `B1` 的 `up (self n)` 子句, `up zero` 的 `toFlo` 参数.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3NBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; z<suc)
open Restrˢ
open import OCF.Align.UniformS using (kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; ≅ᶻ-sym; ≅ᶻ-trans;
  _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; Rˢ; R→≅ˢ; ≅→Rˢ; R-convˢ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-invˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg; ≅ᶻ-refl₀; ≅ᶻ-reflg; ĉ-reflO;
  two; Lv; Lv-refl; Lv-up; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; ink; inl; inr; liftEv; Run; A; wk; limA; limᵢA; ŝA; ĉA;
  Top; top; bound; Bd; sb; nz; ubd; Fc; evF; iF; FM; MF; FB; cloA; flo; cvFlo; toFlo; repA; fold; Ω̂A; ∅ᴿ;
  _≈ᴿ_; fold-≅0; chainA; _∼ᶠ_; ∼ᶠ-refl; cloR; ≺0)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; ofZ; ofZ-≅)
open import OCF.Align.UniformNF3Base using (Obs; idO; fo; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅; r∅; rΩ̂)
```

## §1 `Goodᴺ` 沿 `≅ᶻ` 搬运

```agda
Goodᴺ-tr : ∀ {x y} → x ≅ᶻ y → Goodᴺ x → Goodᴺ y
Goodᴺ-tr zᶻ     gz     = gz
Goodᴺ-tr (sᶻ d) (gs G) = gs (Goodᴺ-tr d G)
Goodᴺ-tr (lᶻ h) (gl G st) = gl (λ n → Goodᴺ-tr (h n) (G n))
  (λ n → ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (h n) (G n) (Goodᴺ-tr (h n) (G n)))))
         (⊑-trans (st n) (≅→⊑ (forceᴺ-≅ (h (suc n)) (G (suc n)) (Goodᴺ-tr (h (suc n)) (G (suc n)))))))
Goodᴺ-tr {y = ĉᴸ c′ t₀′ g′ o₀′ o′} (ĉᶻ {c = c} {t₀ = t₀} {o₀ = o₀} {g = g} {o = o} ec dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′
  where
  dy′ : ∀ m → c′ ⊑ᴵ toLevel (ys m) (hy m)
  dy′ m = ⊑ᴵ-≅ˡ ec (dy m)
  G₀′ : Goodᴺ t₀′
  G₀′ = Goodᴺ-tr dt G₀
  l₀′ : forceᴺ t₀′ G₀′ ≅ ys 0
  l₀′ = ≅-trans (≅-sym (forceᴺ-≅ dt G₀ G₀′)) l₀
  dgm : ∀ m → g (toLevel (ys m) (hy m)) (dy m) ≅ᶻ g′ (toLevel (ys m) (hy m)) (dy′ m)
  dgm m = dg _ (dy m) _ (dy′ m) (≅ᴵ-refl _)
  Gg′ : ∀ m → Goodᴺ (g′ (toLevel (ys m) (hy m)) (dy′ m))
  Gg′ m = Goodᴺ-tr (dgm m) (Gg m)
  lE′ : ∀ m → forceᴺ _ (Gg′ m) ≅ ys (suc m)
  lE′ m = ≅-trans (≅-sym (forceᴺ-≅ (dgm m) (Gg m) (Gg′ m))) (lE m)
  Go₀′ : Goodᴺ o₀′
  Go₀′ = Goodᴺ-tr dp Go₀
  dOk : ∀ k → o (toLevel (ys k) (hy k)) (dy k) ≅ᶻ o′ (toLevel (ys k) (hy k)) (dy′ k)
  dOk k = dO _ (dy k) _ (dy′ k) (≅ᴵ-refl _)
  Go′ : ∀ k → Goodᴺ (o′ (toLevel (ys k) (hy k)) (dy′ k))
  Go′ k = Goodᴺ-tr (dOk k) (Go k)
  mo₀′ : forceᴺ o₀′ Go₀′ ⊑⁰ forceᴺ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ dp Go₀ Go₀′))) (⊑-trans mo₀ (≅→⊑ (forceᴺ-≅ (dOk 0) (Go 0) (Go′ 0))))
  mo′ : ∀ k → forceᴺ _ (Go′ k) ⊑⁰ forceᴺ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (dOk k) (Go k) (Go′ k)))) (⊑-trans (mo k) (≅→⊑ (forceᴺ-≅ (dOk (suc k)) (Go (suc k)) (Go′ (suc k)))))
```

## §2 观测前序与规则 (`Goodᴺ` 版)

```agda
infix 4 _⊑ᵒ_
_⊑ᵒ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ →
  (G : Goodᴺ (toZ (run O x))) (G′ : Goodᴺ (toZ (run O′ y))) → forceᴺ _ G ⊑ forceᴺ _ G′

≅→⊑ᵒ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᵒ y
≅→⊑ᵒ e o G G′ = ≅→⊑ (forceᴺ-≅ (toZ-≅ (run-≅ o e)) G G′)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᵒ y → y ≅ˢ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o G G′ = ⊑-trans (h o G Gm) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

fold-cong : ∀ {fl φ φ′ k k′ i ℓ ℓ′} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L}
            {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
            P ≈ᴿ P → x ⊑ᵒ y → fold 0 φ cv P x ev p ⊑ᵒ fold 0 φ′ cv′ P y ev′ p′
fold-cong r h o = h (fo o r)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           kd ℓ ≡ kd ℓ′ → a ≅ˢ a′ → x ⊑ᵒ y → addˢ a σ x ⊑ᵒ addˢ a′ σ′ y
add-cong k e h o = h (addo o k e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᵒ y → trˢ e x ⊑ᵒ trˢ e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᵒ y → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᵒ y → Ord₊ˢ.up r x ⊑ᵒ y
up-l {r = zero}   h (fo o rP)     = h (fo o rP)
up-l {r = zero}   h (addo o k e) = h (addo o k e)
up-l {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-l {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-l {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (fo o rP)     = h (fo o rP)
up-l {r = self n} h (addo o k e) = h (addo o k e)
up-l {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-l {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-l {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᵒ outˢ (◃₁→◃ r) y → x ⊑ᵒ Ord₊ˢ.up r y
up-r {r = zero}   h (fo o rP)     = h (fo o rP)
up-r {r = zero}   h (addo o k e) = h (addo o k e)
up-r {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-r {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-r {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (fo o rP)     = h (fo o rP)
up-r {r = self n} h (addo o k e) = h (addo o k e)
up-r {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-r {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-r {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o

lim-r : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᵒ h n → x ⊑ᵒ Ord₊ˢ.lim h
lim-r n p idO G (gl G′ st) = ⊑-lim n (p idO G (G′ n))
lim-r {h = h} n p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-r {h = λ m → fold 0 φ′ cv′ P (h m) ev′ p′} n (fold-cong r p) o
lim-r {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-r {h = λ m → addˢ a′ σ′ (h m)} n (add-cong k a p) o
lim-r {h = h} n p (tro {e′ = e′} o)  = lim-r {h = λ m → trˢ e′ (h m)} n (tr-cong p) o
lim-r {h = h} n p (tr⁻o {e′ = e′} o) = lim-r {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordˢ k} {y : Ordˢ k′} → (∀ n → h n ⊑ᵒ y) → Ord₊ˢ.lim h ⊑ᵒ y
lim-l K idO (gl G st) G′ = lim-⊑ (λ n → K n idO (G n) G′)
lim-l {h = h} {y = y} K (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  lim-l {h = λ m → fold 0 φ cv P (h m) ev p} {y = fold 0 φ′ cv′ P y ev′ p′} (λ n o′ → K n (fo o′ r)) o
lim-l {h = h} {y = y} K (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) =
  lim-l {h = λ m → addˢ a σ (h m)} {y = addˢ a′ σ′ y} (λ n o′ → K n (addo o′ k ea)) o
lim-l {h = h} {y = y} K (tro {e = e} {e′ = e′} o)  =
  lim-l {h = λ m → trˢ e (h m)} {y = trˢ e′ y} (λ n o′ → K n (tro o′)) o
lim-l {h = h} {y = y} K (tr⁻o {e = e} {e′ = e′} o) =
  lim-l {h = λ m → tr⁻ˢ e (h m)} {y = tr⁻ˢ e′ y} (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᵒ y → x ⊑ᵒ Ord₊ˢ.suc y
suc-r p idO G (gs G′) = λ h → ≺s (p idO G G′ h)
suc-r {y = y} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-r {h = iter (fold 0 φ′ cv′ P y ev′ p′ +ˢ_) Ord₊ˢ.zero} 1 (fold-cong r p) o
suc-r {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-r {y = addˢ a′ σ′ y} (add-cong k a p) o
suc-r {y = y} p (tro {e′ = e′} o)  = suc-r {y = trˢ e′ y} (tr-cong p) o
suc-r {y = y} p (tr⁻o {e′ = e′} o) = suc-r {y = tr⁻ˢ e′ y} (tr⁻-cong p) o

ŝ-r : ∀ {k k′ c} {x : Ordˢ k} {t₀ : Ordˢ k′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} → x ⊑ᵒ t₀ → x ⊑ᵒ Ord₊ˢ.ŝ c t₀ g
ĉ-r : ∀ {k k′ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {x : Ordˢ k} {o₀ : Ordˢ k′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} →
      x ⊑ᵒ o₀ → x ⊑ᵒ Ord₊ˢ.ĉᴸ c t₀ g o₀ o
ŝ-r {k′ = zero} p idO G (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′}
      (fold-cong r p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = addˢ a′ σ′ t₀} {o = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tro {e′ = e′} o)  = ŝ-r {c = c} {t₀ = trˢ e′ t₀} {g = λ η d → trˢ e′ (g η d)} (tr-cong p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tr⁻o {e′ = e′} o) = ŝ-r {c = c} {t₀ = tr⁻ˢ e′ t₀} {g = λ η d → tr⁻ˢ e′ (g η d)} (tr⁻-cong p) o
ĉ-r p idO G (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o′ r) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = fold 0 φ′ cv′ P o₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (o η e) ev′ p′} (fold-cong r p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (addo {a′ = a′} {σ′ = σ′} o′ k a) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = addˢ a′ σ′ o₀} {o = λ η e → addˢ a′ σ′ (o η e)} (add-cong k a p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tro {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = trˢ e′ o₀} {o = λ η d → trˢ e′ (o η d)} (tr-cong p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tr⁻o {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = tr⁻ˢ e′ o₀} {o = λ η d → tr⁻ˢ e′ (o η d)} (tr⁻-cong p) o′

limᵢ-r : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᵒ g (intoˢ (<→◃ q) z)) → x ⊑ᵒ Ord₊ˢ.limᵢ q g
limᵢ-r {q = ()} H idO
limᵢ-r {j = j} {x = x} {q = q} {g = g} H
       (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r)
  with <ᴵ-dec (cv′ (proj₂ ev′) q) p′
... | injᵃ (via e s) = limᵢ-r (λ z d →
        subst (λ u → fold 0 φ cv P x ev p ⊑ᵒ fold 0 φ′ cv′ P (g (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (fold-cong r (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (fold-cong r (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-r 0 (fold-cong r (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-r (λ z d →
  subst (λ u → addˢ a σ x ⊑ᵒ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-cong k ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → trˢ e x ⊑ᵒ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-cong (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-cong (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o

B1 : ∀ {fl φ k k₀ i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k₀} →
     P ≈ᴿ P → x ⊑ᵒ P (proj₁ ev) p → (y : Ordˢ k) → y ≅ˢ y → x ⊑ᵒ fold 0 φ cv P y ev p
B1 r h Ord₊ˢ.zero e = h
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.suc a) e = lim-r 1 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h a (s-invˢ e))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.lim f) e = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (f 0) (l-invˢ e 0))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {x = x} r h (Ord₊ˢ.limᵢ {i = j′} q g) e with <ᴵ-dec (cv (proj₂ ev) q) p
... | injᵃ (via e₁ s) = limᵢ-r (λ z d →
        subst (λ u → x ⊑ᵒ fold 0 φ cv P (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ev p) (sym (out-intoˢ (<→◃ s) z))
              (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1 {k = suc k′} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up zero y) e =
  B1 {φ = flo k′} {P = P} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))} {p = p} r h y (u-reflˢ zero e)
B1 {φ = φ} {k = lim f s} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up (self n) y) e =
  B1 {φ = flo (f n)} {P = P} {cv = cvFlo (f n)} {ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))} {p = p} r h y (u-reflˢ (self n) e)
B1 {φ = φ} {k = zero} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {k = suc _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {k = lim _ _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h o₀ (ĉ-refl₀ e))

add-r : ∀ {k ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordˢ k) → a ≅ˢ a′ → b ≅ˢ b → a ⊑ᵒ addˢ a′ σ b
add-r Ord₊ˢ.zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (Ord₊ˢ.suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-invˢ eb))
add-r {σ = σ} (Ord₊ˢ.lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-invˢ eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (Ord₊ˢ.limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ addˢ a′ σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (intoˢ (<→◃ q) z)) ea (i-respˢ eb (≅ˢ-reflˡ d))))
add-r {σ = σ} (Ord₊ˢ.up zero x)     ea eb = add-r {σ = λ q → σ (suc q)} x ea (u-reflˢ zero eb)
add-r {σ = σ} (Ord₊ˢ.up (self n) x) ea eb = add-r {σ = λ q → σ (lim n q)} x ea (u-reflˢ (self n) eb)
add-r {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ĉ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) ea eb = ĉ-r (add-r {σ = σ} o₀ ea (ĉ-refl₀ eb))

zero-l : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᵒ y
zero-l ey idO gz G′ = λ ()
zero-l {y = y} ey (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  B1 {φ = φ′} {P = P} {cv = cv′} {ev = ev′} {p = p′} {x = P (proj₁ ev) p} r (≅→⊑ᵒ (r (proj₁ ev) p (proj₁ ev′) p′ (≅ᴵ-refl _))) y ey o
zero-l {y = y} ey (addo {σ′ = σ′} o k ea) = add-r {σ = σ′} y ea ey o
zero-l ey (tro {b = b} {e′ = e′} o)  = zero-l {k = b} (self-trˢ e′ ey) o
zero-l ey (tr⁻o {a = a} {e′ = e′} o) = zero-l {k = a} (self-tr⁻ˢ e′ ey) o

Ω0 : ∀ b → Ωˢ zero ⊑ᵒ Ωˢ b
Ω0 zero      = ≅→⊑ᵒ (Ωˢ-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω0 b) (≅ˢ-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r {r = self 0} (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᵒ Ωˢ b
Ω< e zero      = ≅→⊑ᵒ (Ωˢ-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω< e q) (≅ˢ-sym d)))
Ω< e (lim n q) = lim-r n (up-r {r = self n} (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ωˢ a ⊑ᵒ Ωˢ b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l {r = self n} (Ω-monoᵒ (k n)))

rule4ᵒ : ∀ {ℓ} {c : Ordˢ ℓ} → c ≅ˢ c → ∀ n → iter (c +ˢ_) Ord₊ˢ.zero n ⊑ᵒ iter (c +ˢ_) Ord₊ˢ.zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong refl ec (rule4ᵒ ec n)

```

## §3 地板、严格、覆盖与支配 (`Goodᴺ` 版)

```agda
FlΛ : Ordᴵ → ∀ {k} → Ordˢ k → Set
FlΛ φ t = Ωˢ φ ⊑ᵒ t

FlR : ∀ {fl} → Run fl → Set
FlR {fl} P = ∀ {φ i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → φ ⊑ᴵ i → FlΛ φ (P ev p)

FlΛ-fold : ∀ {fl φ φ₀ k i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} →
           P ≈ᴿ P → FlR P → φ₀ ⊑ᴵ i → (y : Ordˢ k) → y ≅ˢ y → FlΛ φ₀ (fold 0 φ cv P y ev p)
FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r fP h y ey = B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r (fP (proj₁ ev) p h) y ey

FlR-∅ : FlR ∅ᴿ
FlR-∅ ev p h = Ω-monoᵒ h

FlR-Ω̂ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → FlR P → FlR (Ω̂A 0 P)
FlR-Ω̂ {P = P} r fP ev p h = ŝ-r (FlΛ-fold {φ = fk zero} {P = P} {cv = λ e → e} {ev = ev} {p = p} r fP h (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

add-floor : ∀ {k ℓ ℓ₀} {x : Ordˢ ℓ₀} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → x ⊑ᵒ a → b ≅ˢ b → x ⊑ᵒ addˢ a σ b
add-floor Ord₊ˢ.zero h eb = h
add-floor {σ = σ} (Ord₊ˢ.suc b) h eb = suc-r (add-floor {σ = σ} b h (s-invˢ eb))
add-floor {σ = σ} (Ord₊ˢ.lim f) h eb = lim-r 0 (add-floor {σ = σ} (f 0) h (l-invˢ eb 0))
add-floor {x = x} {a = a} {σ = σ} (Ord₊ˢ.limᵢ q g) h eb = limᵢ-r (λ z d →
  subst (λ u → x ⊑ᵒ addˢ a σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-floor {σ = σ} (g (intoˢ (<→◃ q) z)) h (i-respˢ eb (≅ˢ-reflˡ d))))
add-floor {σ = σ} (Ord₊ˢ.up zero y) h eb     = add-floor {σ = λ q → σ (suc q)} y h (u-reflˢ zero eb)
add-floor {σ = σ} (Ord₊ˢ.up (self n) y) h eb = add-floor {σ = λ q → σ (lim n q)} y h (u-reflˢ (self n) eb)
add-floor {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ĉ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) h eb = ĉ-r (add-floor {σ = σ} o₀ h (ĉ-refl₀ eb))

FlΛ-add : ∀ {φ k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → FlΛ φ a → b ≅ˢ b → FlΛ φ (addˢ a σ b)
FlΛ-add b h eb = add-floor b h eb

Strict₀ : ∀ {fl φ k ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ} →
          P ≈ᴿ P → FlR P → (y : Ordˢ k) → y ≅ˢ y → (G : Goodᴺ (toZ (fold 0 φ cv P y ev z))) →
          suc zero ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)
Strict₀ {φ = φ} {P = P} {cv = cv} {ev = ev} {z = z} r fP y ey G =
  toLevel-⊑ (hs hz) (forceᴺ-HS _ G) (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = z} r fP z⊑ y ey idO (gs gz) G)

χ̂ : ∀ {fl} (P : Run fl) (φ : Ordᴵ) {ℓ} → Ev ℓ (fl ⊔ flo φ) → zero <ᴵ ℓ → Ordˢ zero
χ̂ P φ ev z = fold 0 (flo φ) (cvFlo φ) P (Ωˢ φ) ev z

CovΛ : ∀ {fl} (P : Run fl) (φ c : Ordᴵ) → Set
CovΛ {fl} P φ c = Σ Ordᴵ λ ℓ → Σ (Ev ℓ (fl ⊔ flo φ)) λ ev → Σ (zero <ᴵ ℓ) λ z →
                  Σ (Goodᴺ (toZ (χ̂ P φ ev z))) λ G → c ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

data IsCol {fl} (P : Run fl) : ∀ {k} → Obs k → Set where
  col  : ∀ {k ℓ φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ} → IsCol P (fo φ idO P cv ev z)
  ctr  : ∀ {a b} {O : Obs b} {e : a ≅ᴵ b} → IsCol P O → IsCol P (tro O e)
  ctr⁻ : ∀ {a b} {O : Obs a} {e : a ≅ᴵ b} → IsCol P O → IsCol P (tr⁻o O e)

ColC : ∀ {fl} (P : Run fl) {k} → Ordᴵ → Ordˢ k → Set
ColC P {k} c t = ∀ {O : Obs k} → IsCol P O → (G : Goodᴺ (toZ (run O t))) → c ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

ColC-tr : ∀ {fl} {P : Run fl} {c a b} (e : a ≅ᴵ b) {t : Ordˢ a} → ColC P c t → ColC P c (trˢ e t)
ColC-tr e h k G = h (ctr k) G

ColC-tr⁻ : ∀ {fl} {P : Run fl} {c a b} (e : a ≅ᴵ b) {t : Ordˢ b} → ColC P c t → ColC P c (tr⁻ˢ e t)
ColC-tr⁻ e h k G = h (ctr⁻ k) G

canΛ : ∀ {fl} (P : Run fl) (φ : Ordᴵ) {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} → IsCol P O → Obs φ
canΛ P φ ev z col      = fo (flo φ) idO P (cvFlo φ) ev z
canΛ P φ ev z (ctr k)  = tro (canΛ P φ ev z k) (≅ᴵ-refl φ)
canΛ P φ ev z (ctr⁻ k) = tr⁻o (canΛ P φ ev z k) (≅ᴵ-refl φ)

canΛ-≈ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ φ {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} (c : IsCol P O) →
         canΛ P φ ev z c ≈ᵒ O
canΛ-≈ r φ ev z col      = fo idO r
canΛ-≈ r φ ev z (ctr k)  = tro (canΛ-≈ r φ ev z k)
canΛ-≈ r φ ev z (ctr⁻ k) = tr⁻o (canΛ-≈ r φ ev z k)

canΛ-run : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ φ {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} (c : IsCol P O)
           {x : Ordˢ φ} → x ≅ˢ Ωˢ φ → run (canΛ P φ ev z c) x ≅ˢ χ̂ P φ ev z
canΛ-run r φ ev z col      ex = fold-≅0 r ex ev z ev z (≅ᴵ-refl zero)
canΛ-run r φ ev z (ctr k)  ex = canΛ-run r φ ev z k (trˢ-≅ (≅ᴵ-refl φ) ex)
canΛ-run r φ ev z (ctr⁻ k) ex = canΛ-run r φ ev z k (tr⁻ˢ-≅ (≅ᴵ-refl φ) ex)

dom-cov : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ {φ c k} {t : Ordˢ k} → FlΛ φ t → CovΛ P φ c → ColC P c t
dom-cov {P = P} r {φ} {t = t} fl (ℓ , ev , z , G* , d) {O} k G =
  ⊑ᴵ-trans d (toLevel-⊑ (forceᴺ-HS _ G*) (forceᴺ-HS _ G)
                        (⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (≅ˢ-sym rr)) G* G₁)) (fl (canΛ-≈ r φ ev z k) G₁ G)))
  where
  rr : run (canΛ P φ ev z k) (Ωˢ φ) ≅ˢ χ̂ P φ ev z
  rr = canΛ-run r φ ev z k (Ωˢ-refl φ)
  G₁ : Goodᴺ (toZ (run (canΛ P φ ev z k) (Ωˢ φ)))
  G₁ = Goodᴺ-tr (toZ-≅ (≅ˢ-sym rr)) G*

```
