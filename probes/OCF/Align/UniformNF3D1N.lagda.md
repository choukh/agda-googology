# 深度 1 的观测 (二): `Goodᴺ` 上的观测前序

> 由 [UniformNF3NBase](UniformNF3NBase.lagda.md) 经脚本克隆: `fo` 的每个子句得到一个 `fo1` 子句, 文本只差 `fold 0 φ cv P x ev p` 换成 `fold 1 (flo K) (cvFlo K) E x P ev p`. 结论先说:
>
> 1. **规则层对 `fo1` 没有新内容.** `lim`、`limᵢ`、`up`、`ŝ`、`ĉ` 的同余都是克隆. `suc-r` 取第 1 份 (`repA … 1`).
> 2. `B1₁`: 深度 1 折叠的地板是 $E\,Q$ 的地板. `zero-l` 走它.
> 3. 加法的种类前提换成 $\ell\cong\ell'$ (`UniformNF3Eq`).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D1N where

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
open import OCF.Align.UniformNF3Eq using (kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; ≅ᶻ-sym; ≅ᶻ-trans;
  _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; Rˢ; R→≅ˢ; ≅→Rˢ; R-convˢ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-invˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg; ≅ᶻ-refl₀; ≅ᶻ-reflg; ĉ-reflO;
  two; Lv; Lv-refl; Lv-up; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; ink; inl; inr; liftEv; Run; A; wk; limA; limᵢA; ŝA; ĉA; Top; top; bound; Bd; sb; nz; ubd; Fc; evF; iF; FM; MF; FB; cloA; flo; cvFlo; toFlo; repA; fold; Ω̂A; ∅ᴿ; chainA; _∼ᶠ_; ∼ᶠ-refl; ≺0)
open import OCF.Align.UniformNF3Eq using (_≈₁_; _≈ᴿ_; fold-≅0; cloR)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; ofZ; ofZ-≅)
open import OCF.Align.UniformNF3D1O using (Obs; idO; fo; fo1; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅; r∅; rΩ̂)
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

fold1-cong : ∀ {flE fl k k′ i ℓ ℓ′} {E : A 1 flE} {P : Run fl} {ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
             E ≈₁ E → P ≈ᴿ P → x ⊑ᵒ y → fold 1 (flo k) (cvFlo k) E x P ev p ⊑ᵒ fold 1 (flo k′) (cvFlo k′) E y P ev′ p′
fold1-cong rE r h o = h (fo1 o rE r)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → x ⊑ᵒ y → addˢ a σ x ⊑ᵒ addˢ a′ σ′ y
add-cong k e h o = h (addo o k e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᵒ y → trˢ e x ⊑ᵒ trˢ e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᵒ y → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᵒ y → Ord₊ˢ.up r x ⊑ᵒ y
up-l {r = zero}   h (fo o rP)     = h (fo o rP)
up-l {r = zero}   h (fo1 o rE rP)     = h (fo1 o rE rP)
up-l {r = zero}   h (addo o k e) = h (addo o k e)
up-l {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-l {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-l {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (fo o rP)     = h (fo o rP)
up-l {r = self n} h (fo1 o rE rP)     = h (fo1 o rE rP)
up-l {r = self n} h (addo o k e) = h (addo o k e)
up-l {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-l {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-l {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᵒ outˢ (◃₁→◃ r) y → x ⊑ᵒ Ord₊ˢ.up r y
up-r {r = zero}   h (fo o rP)     = h (fo o rP)
up-r {r = zero}   h (fo1 o rE rP)     = h (fo1 o rE rP)
up-r {r = zero}   h (addo o k e) = h (addo o k e)
up-r {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-r {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-r {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (fo o rP)     = h (fo o rP)
up-r {r = self n} h (fo1 o rE rP)     = h (fo1 o rE rP)
up-r {r = self n} h (addo o k e) = h (addo o k e)
up-r {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-r {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-r {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o

lim-r : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᵒ h n → x ⊑ᵒ Ord₊ˢ.lim h
lim-r n p idO G (gl G′ st) = ⊑-lim n (p idO G (G′ n))
lim-r {h = h} n p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-r {h = λ m → fold 0 φ′ cv′ P (h m) ev′ p′} n (fold-cong r p) o
lim-r {h = h} n p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  lim-r {h = λ m → fold 1 (flo K₁′) (cvFlo K₁′) E (h m) P ev′ p′} n (fold1-cong rE r p) o
lim-r {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-r {h = λ m → addˢ a′ σ′ (h m)} n (add-cong k a p) o
lim-r {h = h} n p (tro {e′ = e′} o)  = lim-r {h = λ m → trˢ e′ (h m)} n (tr-cong p) o
lim-r {h = h} n p (tr⁻o {e′ = e′} o) = lim-r {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordˢ k} {y : Ordˢ k′} → (∀ n → h n ⊑ᵒ y) → Ord₊ˢ.lim h ⊑ᵒ y
lim-l K idO (gl G st) G′ = lim-⊑ (λ n → K n idO (G n) G′)
lim-l {h = h} {y = y} K (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  lim-l {h = λ m → fold 0 φ cv P (h m) ev p} {y = fold 0 φ′ cv′ P y ev′ p′} (λ n o′ → K n (fo o′ r)) o
lim-l {h = h} {y = y} K (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) =
  lim-l {h = λ m → fold 1 (flo K₁) (cvFlo K₁) E (h m) P ev p} {y = fold 1 (flo K₁′) (cvFlo K₁′) E y P ev′ p′} (λ n o′ → K n (fo1 o′ rE r)) o
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
suc-r {y = y} p (fo1 {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  lim-r {h = λ m → repA 0 P (fold 1 (flo K₁′) (cvFlo K₁′) E y) m ev′ p′} 1 (fold1-cong rE r p) o
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
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = fold 1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {o = λ η e → fold 1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′}
      (fold1-cong rE r p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ŝ-r {c = c} {t₀ = fold 1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {g = λ η e → fold 1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′} (fold1-cong rE r p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ŝ-r {c = c} {t₀ = fold 1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {g = λ η e → fold 1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′} (fold1-cong rE r p) o
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
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o′ rE r) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = fold 1 (flo K₁′) (cvFlo K₁′) E o₀ P ev′ p′} {o = λ η e → fold 1 (flo K₁′) (cvFlo K₁′) E (o η e) P ev′ p′} (fold1-cong rE r p) o′
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
limᵢ-r {j = j} {x = x} {q = q} {g = g} H
       (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r)
  with <ᴵ-dec (cvFlo K₁′ (proj₂ (proj₂ ev′)) q) p′
... | injᵃ (via e s) = limᵢ-r (λ z d →
        subst (λ u → fold 1 (flo K₁) (cvFlo K₁) E x P ev p ⊑ᵒ fold 1 (flo K₁′) (cvFlo K₁′) E (g (intoˢ (<→◃ q) (tr⁻ˢ e u))) P ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (fold1-cong rE r (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (fold1-cong rE r (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-r 0 (fold1-cong rE r (H (Ωˢ j) (Ωˢ-refl j))) o
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

B1₁ : ∀ {flE fl φ k k₀ i ℓ} {E : A 1 flE} {Q : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ (flE ⊔ φ))} {p : i <ᴵ ℓ} {x : Ordˢ k₀} →
      x ⊑ᵒ E Q (proj₁ ev , proj₁ (proj₂ ev)) p → (y : Ordˢ k) → y ≅ˢ y → x ⊑ᵒ fold 1 φ cv E y Q ev p
B1₁ h Ord₊ˢ.zero e = h
B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.suc a) e = lim-r 1 (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h a (s-invˢ e))
B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.lim f) e = lim-r 0 (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (f 0) (l-invˢ e 0))
B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} {x = x} h (Ord₊ˢ.limᵢ {i = j′} q g) e with <ᴵ-dec (cv (proj₂ (proj₂ ev)) q) p
... | injᵃ (via e₁ s) = limᵢ-r (λ z d →
        subst (λ u → x ⊑ᵒ fold 1 φ cv E (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) Q ev p) (sym (out-intoˢ (<→◃ s) z))
              (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1₁ {k = suc k′} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.up zero y) e =
  B1₁ {φ = flo k′} {E = E} {Q = Q} {cv = cvFlo k′} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))} {p = p} h y (u-reflˢ zero e)
B1₁ {φ = φ} {k = lim f s} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.up (self n) y) e =
  B1₁ {φ = flo (f n)} {E = E} {Q = Q} {cv = cvFlo (f n)} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))} {p = p} h y (u-reflˢ (self n) e)
B1₁ {φ = φ} {k = zero} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ {φ = φ} {k = suc _} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ {φ = φ} {k = lim _ _} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1₁ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h o₀ (ĉ-refl₀ e))

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
zero-l {y = y} ey (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) =
  B1₁ {φ = flo K₁′} {E = E} {Q = P} {cv = cvFlo K₁′} {ev = ev′} {p = p′} {x = E P (proj₁ ev , proj₁ (proj₂ ev)) p} (≅→⊑ᵒ (rE (∼ᶠ-refl _) r (proj₁ ev , proj₁ (proj₂ ev)) p (proj₁ ev′ , proj₁ (proj₂ ev′)) p′ (≅ᴵ-refl _))) y ey o
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
rule4ᵒ ec (suc n) = add-cong (≅ᴵ-refl _) ec (rule4ᵒ ec n)

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
```
