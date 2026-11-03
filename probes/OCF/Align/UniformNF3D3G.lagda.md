# 一切深度 (三): 保存在性前序与严格增长

> 由 [UniformNF3D3G](UniformNF3D3G.lagda.md) 经脚本克隆. 结论先说:
>
> 1. **`FFl {d} E` (§3): 帧的地板, 对一切深度同一个记录.** 它由脊的地板 `SF` 定义: `SF` 按深度递归, 头是一个 `FlU`. 第 0 层的头就是 `PFl`.
> 2. **`suc-fold₁`:** 第 2 份 $F(F\,P)\,s$ 严格高于 $F\,P\,s$, 只读 `stE`; 所以 `Rs`、`Climb`、`Ω-strict` 对任意深度的 `fo1` 成立, 证明不读 $d$.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3G where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_)
open Restrˢ
open import OCF.Align.UniformNF3Eq using (kd; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym;
  _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (A; repA; _∼ᶠ_; ∼ᶠ-refl; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; _⊔_)
open import OCF.Align.UniformNF3Eq using (flo-∼; _≈ᴿ_; fold-≅0)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (Fr; Sp; sf; fold1; rowU; repU; repR; _≈U_; _≈S_; fold-≅U; Obs; idO; fo; fo1; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅; r∅; rΩ̂)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
```

```agda
infix 4 _⊑ᴱ_
_⊑ᴱ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᴱ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
  Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

≅→⊑ᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᴱ y
≅→⊑ᴱ e o G′ = Goodᴺ-tr (≅ᶻ-sym d) G′ , ≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) G′) G′)
  where d = toZ-≅ (run-≅ o e)

⊑ᴱ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᴱ y → y ≅ˢ y′ → x ⊑ᴱ y′
⊑ᴱ-≅ʳ h e o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

⊑ᴱ-trans : ∀ {k k′} {x : Ordˢ k} {y w : Ordˢ k′} → x ⊑ᴱ y → y ⊑ᴱ w → x ⊑ᴱ w
⊑ᴱ-trans h i o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (proj₂ (i (≈ᵒ-reflʳ o) G′))
  where Gm = proj₁ (i (≈ᵒ-reflʳ o) G′)
```

## §2 右引入规则

下面的规则由 UniformNF3D3O §2–§4 的同名规则改写 (后缀 ᴱ), 只有 `idO` 子句不同.

```agda
fold-congᴱ : ∀ {fl φ φ′ k k′ i ℓ ℓ′} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L}
            {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
            P ≈ᴿ P → x ⊑ᴱ y → fold 0 φ cv P x ev p ⊑ᴱ fold 0 φ′ cv′ P y ev′ p′
fold-congᴱ r h o = h (fo o r)

fold1-congᴱ : ∀ {d flE k k′ i ℓ ℓ′} {E : Fr (suc d) flE} {P : Sp (suc d)} {ev : Ev ℓ (sf P ⊔ (flE ⊔ flo k))} {ev′ : Ev ℓ′ (sf P ⊔ (flE ⊔ flo k′))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
              E ≈U E → P ≈S P → x ⊑ᴱ y → fold1 (flo k) (cvFlo k) E x P ev p ⊑ᴱ fold1 (flo k′) (cvFlo k′) E y P ev′ p′
fold1-congᴱ rE r h o = h (fo1 o rE r)

add-congᴱ : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → x ⊑ᴱ y → addˢ a σ x ⊑ᴱ addˢ a′ σ′ y
add-congᴱ k e h o = h (addo o k e)

tr-congᴱ : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᴱ y → trˢ e x ⊑ᴱ trˢ e′ y
tr-congᴱ h o = h (tro o)

tr⁻-congᴱ : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᴱ y → tr⁻ˢ e x ⊑ᴱ tr⁻ˢ e′ y
tr⁻-congᴱ h o = h (tr⁻o o)

up-lᴱ : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᴱ y → Ord₊ˢ.up r x ⊑ᴱ y
up-lᴱ {r = zero}   h (fo o rP)     = h (fo o rP)
up-lᴱ {r = zero}   h (fo1 o rE rP)     = h (fo1 o rE rP)
up-lᴱ {r = zero}   h (addo o k e) = h (addo o k e)
up-lᴱ {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-lᴱ {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-lᴱ {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-lᴱ {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-lᴱ {r = self n} h (fo o rP)     = h (fo o rP)
up-lᴱ {r = self n} h (fo1 o rE rP)     = h (fo1 o rE rP)
up-lᴱ {r = self n} h (addo o k e) = h (addo o k e)
up-lᴱ {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-lᴱ {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-lᴱ {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-lᴱ {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-rᴱ : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᴱ outˢ (◃₁→◃ r) y → x ⊑ᴱ Ord₊ˢ.up r y
up-rᴱ {r = zero}   h (fo o rP)     = h (fo o rP)
up-rᴱ {r = zero}   h (fo1 o rE rP)     = h (fo1 o rE rP)
up-rᴱ {r = zero}   h (addo o k e) = h (addo o k e)
up-rᴱ {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-rᴱ {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-rᴱ {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-rᴱ {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-rᴱ {r = self n} h (fo o rP)     = h (fo o rP)
up-rᴱ {r = self n} h (fo1 o rE rP)     = h (fo1 o rE rP)
up-rᴱ {r = self n} h (addo o k e) = h (addo o k e)
up-rᴱ {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-rᴱ {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-rᴱ {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-rᴱ {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
lim-rᴱ : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᴱ h n → x ⊑ᴱ Ord₊ˢ.lim h
lim-rᴱ n p idO (gl G′ st) = proj₁ (p idO (G′ n)) , ⊑-lim n (proj₂ (p idO (G′ n)))
lim-rᴱ {h = h} n p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-rᴱ {h = λ m → fold 0 φ′ cv′ P (h m) ev′ p′} n (fold-congᴱ r p) o
lim-rᴱ {h = h} n p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  lim-rᴱ {h = λ m → fold1 (flo K₁′) (cvFlo K₁′) E (h m) P ev′ p′} n (fold1-congᴱ rE r p) o
lim-rᴱ {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-rᴱ {h = λ m → addˢ a′ σ′ (h m)} n (add-congᴱ k a p) o
lim-rᴱ {h = h} n p (tro {e′ = e′} o)  = lim-rᴱ {h = λ m → trˢ e′ (h m)} n (tr-congᴱ p) o
lim-rᴱ {h = h} n p (tr⁻o {e′ = e′} o) = lim-rᴱ {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-congᴱ p) o

suc-rᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᴱ y → x ⊑ᴱ Ord₊ˢ.suc y
suc-rᴱ p idO (gs G′) = proj₁ (p idO G′) , λ h → ≺s (proj₂ (p idO G′) h)
suc-rᴱ {y = y} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-rᴱ {h = iter (fold 0 φ′ cv′ P y ev′ p′ +ˢ_) Ord₊ˢ.zero} 1 (fold-congᴱ r p) o
suc-rᴱ {y = y} p (fo1 {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  lim-rᴱ {h = λ m → rowU P (fold1 (flo K₁′) (cvFlo K₁′) E y) m ev′ p′} 1 (fold1-congᴱ rE r p) o
suc-rᴱ {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-rᴱ {y = addˢ a′ σ′ y} (add-congᴱ k a p) o
suc-rᴱ {y = y} p (tro {e′ = e′} o)  = suc-rᴱ {y = trˢ e′ y} (tr-congᴱ p) o
suc-rᴱ {y = y} p (tr⁻o {e′ = e′} o) = suc-rᴱ {y = tr⁻ˢ e′ y} (tr⁻-congᴱ p) o

ŝ-rᴱ : ∀ {k k′ c} {x : Ordˢ k} {t₀ : Ordˢ k′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} → x ⊑ᴱ t₀ → x ⊑ᴱ Ord₊ˢ.ŝ c t₀ g
ĉ-rᴱ : ∀ {k k′ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {x : Ordˢ k} {o₀ : Ordˢ k′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} →
      x ⊑ᴱ o₀ → x ⊑ᴱ Ord₊ˢ.ĉᴸ c t₀ g o₀ o
ŝ-rᴱ {k′ = zero} p idO (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = proj₁ (p idO Go₀) , ⊑-lim 0 (proj₂ (p idO Go₀))
ŝ-rᴱ {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ĉ-rᴱ {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′}
      (fold-congᴱ r p) o
ŝ-rᴱ {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ĉ-rᴱ {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = fold1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {o = λ η e → fold1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′}
      (fold1-congᴱ rE r p) o
ŝ-rᴱ {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-rᴱ {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-congᴱ r p) o
ŝ-rᴱ {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ŝ-rᴱ {c = c} {t₀ = fold1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {g = λ η e → fold1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′} (fold1-congᴱ rE r p) o
ŝ-rᴱ {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-rᴱ {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-congᴱ r p) o
ŝ-rᴱ {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o rE r) =
  ŝ-rᴱ {c = c} {t₀ = fold1 (flo K₁′) (cvFlo K₁′) E t₀ P ev′ p′} {g = λ η e → fold1 (flo K₁′) (cvFlo K₁′) E (g η e) P ev′ p′} (fold1-congᴱ rE r p) o
ŝ-rᴱ {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ĉ-rᴱ {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = addˢ a′ σ′ t₀} {o = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-rᴱ {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-rᴱ {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {c = c} {t₀ = t₀} {g = g} p (tro {e′ = e′} o)  = ŝ-rᴱ {c = c} {t₀ = trˢ e′ t₀} {g = λ η d → trˢ e′ (g η d)} (tr-congᴱ p) o
ŝ-rᴱ {c = c} {t₀ = t₀} {g = g} p (tr⁻o {e′ = e′} o) = ŝ-rᴱ {c = c} {t₀ = tr⁻ˢ e′ t₀} {g = λ η d → tr⁻ˢ e′ (g η d)} (tr⁻-congᴱ p) o
ĉ-rᴱ p idO (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = proj₁ (p idO Go₀) , ⊑-lim 0 (proj₂ (p idO Go₀))
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o′ r) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = fold 0 φ′ cv′ P o₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (o η e) ev′ p′} (fold-congᴱ r p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev′ = ev′} {p′ = p′} o′ rE r) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = fold1 (flo K₁′) (cvFlo K₁′) E o₀ P ev′ p′} {o = λ η e → fold1 (flo K₁′) (cvFlo K₁′) E (o η e) P ev′ p′} (fold1-congᴱ rE r p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (addo {a′ = a′} {σ′ = σ′} o′ k a) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = addˢ a′ σ′ o₀} {o = λ η e → addˢ a′ σ′ (o η e)} (add-congᴱ k a p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tro {e′ = e′} o′) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = trˢ e′ o₀} {o = λ η d → trˢ e′ (o η d)} (tr-congᴱ p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tr⁻o {e′ = e′} o′) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = tr⁻ˢ e′ o₀} {o = λ η d → tr⁻ˢ e′ (o η d)} (tr⁻-congᴱ p) o′

limᵢ-rᴱ : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᴱ g (intoˢ (<→◃ q) z)) → x ⊑ᴱ Ord₊ˢ.limᵢ q g
limᵢ-rᴱ {q = ()} H idO
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H
       (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r)
  with <ᴵ-dec (cv′ (proj₂ ev′) q) p′
... | injᵃ (via e s) = limᵢ-rᴱ (λ z d →
        subst (λ u → fold 0 φ cv P x ev p ⊑ᴱ fold 0 φ′ cv′ P (g (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (fold-congᴱ r (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-rᴱ 0 (fold-congᴱ r (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-rᴱ 0 (fold-congᴱ r (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H
       (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r)
  with <ᴵ-dec (cvFlo K₁′ (proj₂ (proj₂ ev′)) q) p′
... | injᵃ (via e s) = limᵢ-rᴱ (λ z d →
        subst (λ u → fold1 (flo K₁) (cvFlo K₁) E x P ev p ⊑ᴱ fold1 (flo K₁′) (cvFlo K₁′) E (g (intoˢ (<→◃ q) (tr⁻ˢ e u))) P ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (fold1-congᴱ rE r (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-rᴱ 0 (fold1-congᴱ rE r (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-rᴱ 0 (fold1-congᴱ rE r (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-rᴱ (λ z d →
  subst (λ u → addˢ a σ x ⊑ᴱ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-congᴱ k ea (H z d))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → trˢ e x ⊑ᴱ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-congᴱ (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᴱ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-congᴱ (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o
B1ᴱ : ∀ {fl φ k k₀ i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k₀} →
     P ≈ᴿ P → x ⊑ᴱ P (proj₁ ev) p → (y : Ordˢ k) → y ≅ˢ y → x ⊑ᴱ fold 0 φ cv P y ev p
B1ᴱ r h Ord₊ˢ.zero e = h
B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.suc a) e = lim-rᴱ 1 (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h a (s-invˢ e))
B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.lim f) e = lim-rᴱ 0 (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (f 0) (l-invˢ e 0))
B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {x = x} r h (Ord₊ˢ.limᵢ {i = j′} q g) e with <ᴵ-dec (cv (proj₂ ev) q) p
... | injᵃ (via e₁ s) = limᵢ-rᴱ (λ z d →
        subst (λ u → x ⊑ᴱ fold 0 φ cv P (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ev p) (sym (out-intoˢ (<→◃ s) z))
              (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-rᴱ 0 (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-rᴱ 0 (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1ᴱ {k = suc k′} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up zero y) e =
  B1ᴱ {φ = flo k′} {P = P} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))} {p = p} r h y (u-reflˢ zero e)
B1ᴱ {φ = φ} {k = lim f s} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up (self n) y) e =
  B1ᴱ {φ = flo (f n)} {P = P} {cv = cvFlo (f n)} {ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))} {p = p} r h y (u-reflˢ (self n) e)
B1ᴱ {φ = φ} {k = zero} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-rᴱ (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1ᴱ {φ = φ} {k = suc _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-rᴱ (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1ᴱ {φ = φ} {k = lim _ _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-rᴱ (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-rᴱ (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h o₀ (ĉ-refl₀ e))
B1₁ᴱ : ∀ {d flE φ k k₀ i ℓ} {E : Fr (suc d) flE} {Q : Sp (suc d)} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ φ))} {p : i <ᴵ ℓ} {x : Ordˢ k₀} →
       x ⊑ᴱ E Q (proj₁ ev , proj₁ (proj₂ ev)) p → (y : Ordˢ k) → y ≅ˢ y → x ⊑ᴱ fold1 φ cv E y Q ev p
B1₁ᴱ h Ord₊ˢ.zero e = h
B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.suc a) e = lim-rᴱ 1 (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h a (s-invˢ e))
B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.lim f) e = lim-rᴱ 0 (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (f 0) (l-invˢ e 0))
B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} {x = x} h (Ord₊ˢ.limᵢ {i = j′} q g) e with <ᴵ-dec (cv (proj₂ (proj₂ ev)) q) p
... | injᵃ (via e₁ s) = limᵢ-rᴱ (λ z d →
        subst (λ u → x ⊑ᴱ fold1 φ cv E (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) Q ev p) (sym (out-intoˢ (<→◃ s) z))
              (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-rᴱ 0 (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-rᴱ 0 (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1₁ᴱ {k = suc k′} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.up zero y) e =
  B1₁ᴱ {φ = flo k′} {E = E} {Q = Q} {cv = cvFlo k′} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))} {p = p} h y (u-reflˢ zero e)
B1₁ᴱ {φ = φ} {k = lim f s} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.up (self n) y) e =
  B1₁ᴱ {φ = flo (f n)} {E = E} {Q = Q} {cv = cvFlo (f n)} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))} {p = p} h y (u-reflˢ (self n) e)
B1₁ᴱ {φ = φ} {k = zero} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-rᴱ (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ᴱ {φ = φ} {k = suc _} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-rᴱ (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ᴱ {φ = φ} {k = lim _ _} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-rᴱ (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h t₀ (ŝ-refl₀ e))
B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-rᴱ (B1₁ᴱ {φ = φ} {E = E} {Q = Q} {cv = cv} {ev = ev} {p = p} h o₀ (ĉ-refl₀ e))

add-rᴱ : ∀ {k ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordˢ k) → a ≅ˢ a′ → b ≅ˢ b → a ⊑ᴱ addˢ a′ σ b
add-rᴱ Ord₊ˢ.zero ea eb = ≅→⊑ᴱ ea
add-rᴱ {σ = σ} (Ord₊ˢ.suc b) ea eb = suc-rᴱ (add-rᴱ {σ = σ} b ea (s-invˢ eb))
add-rᴱ {σ = σ} (Ord₊ˢ.lim h) ea eb = lim-rᴱ 0 (add-rᴱ {σ = σ} (h 0) ea (l-invˢ eb 0))
add-rᴱ {a = a} {a′ = a′} {σ = σ} (Ord₊ˢ.limᵢ q g) ea eb = limᵢ-rᴱ (λ z d →
  subst (λ u → a ⊑ᴱ addˢ a′ σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-rᴱ {σ = σ} (g (intoˢ (<→◃ q) z)) ea (i-respˢ eb (≅ˢ-reflˡ d))))
add-rᴱ {σ = σ} (Ord₊ˢ.up zero x)     ea eb = add-rᴱ {σ = λ q → σ (suc q)} x ea (u-reflˢ zero eb)
add-rᴱ {σ = σ} (Ord₊ˢ.up (self n) x) ea eb = add-rᴱ {σ = λ q → σ (lim n q)} x ea (u-reflˢ (self n) eb)
add-rᴱ {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ĉ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) ea eb = ĉ-rᴱ (add-rᴱ {σ = σ} o₀ ea (ĉ-refl₀ eb))

zero-lᴱ : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᴱ y
zero-lᴱ ey idO G′ = gz , λ ()
zero-lᴱ {y = y} ey (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  B1ᴱ {φ = φ′} {P = P} {cv = cv′} {ev = ev′} {p = p′} {x = P (proj₁ ev) p} r (≅→⊑ᴱ (r (proj₁ ev) p (proj₁ ev′) p′ (≅ᴵ-refl _))) y ey o
zero-lᴱ {y = y} ey (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) =
  B1₁ᴱ {φ = flo K₁′} {E = E} {Q = P} {cv = cvFlo K₁′} {ev = ev′} {p = p′} {x = E P (proj₁ ev , proj₁ (proj₂ ev)) p} (≅→⊑ᴱ (rE r (proj₁ ev , proj₁ (proj₂ ev)) p (proj₁ ev′ , proj₁ (proj₂ ev′)) p′ (≅ᴵ-refl _))) y ey o
zero-lᴱ {y = y} ey (addo {σ′ = σ′} o k ea) = add-rᴱ {σ = σ′} y ea ey o
zero-lᴱ ey (tro {b = b} {e′ = e′} o)  = zero-lᴱ {k = b} (self-trˢ e′ ey) o
zero-lᴱ ey (tr⁻o {a = a} {e′ = e′} o) = zero-lᴱ {k = a} (self-tr⁻ˢ e′ ey) o

Ω0ᴱ : ∀ b → Ωˢ zero ⊑ᴱ Ωˢ b
Ω0ᴱ zero      = ≅→⊑ᴱ (Ωˢ-refl zero)
Ω0ᴱ (suc b)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω0ᴱ b) (≅ˢ-sym d)))
Ω0ᴱ (lim g s) = lim-rᴱ 0 (up-rᴱ {r = self 0} (Ω0ᴱ (g 0)))

add-floorᴱ : ∀ {k ℓ ℓ₀} {x : Ordˢ ℓ₀} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → x ⊑ᴱ a → b ≅ˢ b → x ⊑ᴱ addˢ a σ b
add-floorᴱ Ord₊ˢ.zero h eb = h
add-floorᴱ {σ = σ} (Ord₊ˢ.suc b) h eb = suc-rᴱ (add-floorᴱ {σ = σ} b h (s-invˢ eb))
add-floorᴱ {σ = σ} (Ord₊ˢ.lim f) h eb = lim-rᴱ 0 (add-floorᴱ {σ = σ} (f 0) h (l-invˢ eb 0))
add-floorᴱ {x = x} {a = a} {σ = σ} (Ord₊ˢ.limᵢ q g) h eb = limᵢ-rᴱ (λ z d →
  subst (λ u → x ⊑ᴱ addˢ a σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-floorᴱ {σ = σ} (g (intoˢ (<→◃ q) z)) h (i-respˢ eb (≅ˢ-reflˡ d))))
add-floorᴱ {σ = σ} (Ord₊ˢ.up zero y) h eb     = add-floorᴱ {σ = λ q → σ (suc q)} y h (u-reflˢ zero eb)
add-floorᴱ {σ = σ} (Ord₊ˢ.up (self n) y) h eb = add-floorᴱ {σ = λ q → σ (lim n q)} y h (u-reflˢ (self n) eb)
add-floorᴱ {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ĉ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) h eb = ĉ-rᴱ (add-floorᴱ {σ = σ} o₀ h (ĉ-refl₀ eb))

```

## §3 上下文: 带地板的前缀与加法

`PFl P`: 前缀的自互模拟与两条地板. `f0`: 值 $\sqsupseteq\Omega_i$. `fS`: 非零尾巴的折叠 $\sqsupseteq\Omega_i+1$; 这是严格增长的来源, 空前缀与 $\Omega_\Omega$ 闭包都满足 (§7). `Ctx O`: 栈里每个折叠的前缀都有 `PFl`, 每个加法的左项 $\sqsupseteq1$. 本文的上下文不含搬运 (`Ctx` 在 `tro`/`tr⁻o` 处为空), 见文末边界.

```agda
σ₀ : ∀ {ℓ} → Simᴵ zero ℓ
σ₀ ()

𝟏 : Ordˢ zero
𝟏 = Ord₊ˢ.suc Ord₊ˢ.zero

Ω1ᴱ : ∀ b → 𝟏 ⊑ᴱ Ωˢ b
Ω1ᴱ zero      = ≅→⊑ᴱ (s≅ z≅ z≅)
Ω1ᴱ (suc b)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ b) (≅ˢ-sym d)))
Ω1ᴱ (lim g s) = lim-rᴱ 0 (up-rᴱ {r = self 0} (Ω1ᴱ (g 0)))

record PFl {fl} (P : Run fl) : Set where
  constructor pfl
  field
    rP : P ≈ᴿ P
    f0 : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Ωˢ i ⊑ᴱ P ev p
    fS : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fl ⊔ φ)) (p : i <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y →
         𝟏 ⊑ᴱ y → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ fold 0 φ cv P y ev p

record FFlP {d flE} (FH : ∀ {fl} → Fr d fl → Set) (SS : Sp d → Set) (E : Fr (suc d) flE) : Set where
  constructor ffl
  field
    rE  : E ≈U E
    pE  : ∀ {Q : Sp (suc d)} → (FH (proj₁ (proj₂ Q)) × SS (proj₂ (proj₂ Q))) → PFl (E Q)
    s1E : ∀ {Q : Sp (suc d)} → (FH (proj₁ (proj₂ Q)) × SS (proj₂ (proj₂ Q))) → ∀ {i ℓ} (ev : Ev ℓ (sf Q ⊔ flE)) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ E Q ev p
    stE : ∀ {Q : Sp (suc d)} → (FH (proj₁ (proj₂ Q)) × SS (proj₂ (proj₂ Q))) → ∀ {i ℓ} (ev : Ev ℓ (sf Q ⊔ flE)) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (proj₁ (proj₂ Q) (proj₂ (proj₂ Q)) (proj₁ ev) p) ⊑ᴱ E Q ev p

mutual
  FlU : ∀ (d : ℕ) {φ} → Fr d φ → Set
  FlU zero    P = PFl (P tt)
  FlU (suc d) E = FFlP (FlU d) (SF {d}) E

  SF : ∀ {d : ℕ} → Sp d → Set
  SF {d = zero}  _ = ⊤
  SF {d = suc d} Q = FlU d (proj₁ (proj₂ Q)) × SF (proj₂ (proj₂ Q))

FFl : ∀ {d flE} → Fr (suc d) flE → Set
FFl {d} E = FlU (suc d) E
module FFl = FFlP

FlU≈ : ∀ d {φ} {P : Fr d φ} → FlU d P → P ≈U P
SF≈ : ∀ {d} {s : Sp d} → SF s → s ≈S s
FlU≈ zero    h _ = PFl.rP h
FlU≈ (suc d) h = FFl.rE h
SF≈ {d = zero}  _ = tt
SF≈ {d = suc d} {s} (h , t) = ∼ᶠ-refl (proj₁ s) , FlU≈ d h , SF≈ t

record AFl {ℓ} (a : Ordˢ ℓ) : Set where
  constructor afl
  field
    ea  : a ≅ˢ a
    one : 𝟏 ⊑ᴱ a

Ctx : ∀ {k} → Obs k → Set
Ctx idO                = ⊤
Ctx (fo φ O P cv ev p) = PFl P × Ctx O
Ctx (fo1 O E Q ev p)   = FFl E × (SF Q × Ctx O)
Ctx (addo O a σ)       = AFl a × Ctx O
Ctx (tro O e)          = Ctx O
Ctx (tr⁻o O e)         = Ctx O

ctx-refl : ∀ {k} (O : Obs k) → Ctx O → O ≈ᵒ O
ctx-refl idO _ = idO
ctx-refl (fo φ O P cv ev p) (pfl r _ _ , c) = fo (ctx-refl O c) r
ctx-refl (fo1 O E Q ev p) (fE , pf , c) = fo1 (ctx-refl O c) (FFl.rE fE) (SF≈ pf)
ctx-refl (addo O a σ) (afl e _ , c) = addo (ctx-refl O c) (≅ᴵ-refl _) e
ctx-refl (tro O e) c = tro (ctx-refl O c)
ctx-refl (tr⁻o O e) c = tr⁻o (ctx-refl O c)

suc-fold : ∀ {fl φ k i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {a : Ordˢ k} →
           P ≈ᴿ P → (∀ {i′ ℓ′} (ev′ : Ev ℓ′ fl) (p′ : i′ <ᴵ ℓ′) → Ωˢ i′ ⊑ᴱ P ev′ p′) → a ≅ˢ a →
           Ord₊ˢ.suc (fold 0 φ cv P a ev p) ⊑ᴱ fold 0 φ cv P (Ord₊ˢ.suc a) ev p
suc-fold {φ = φ} {i = i} {P = P} {cv = cv} {ev = ev} {p = p} {a = a} r f0 ea =
  lim-rᴱ {h = iter (w +ˢ_) Ord₊ˢ.zero} 2
    (add-congᴱ {a = w} {a′ = w} {σ = σ₀} {σ′ = λ q → q} {x = 𝟏} {y = w} (≅ᴵ-refl _) ew
       (B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {x = 𝟏} r (⊑ᴱ-trans (Ω1ᴱ i) (f0 (proj₁ ev) p)) a ea))
  where
  w  = fold 0 φ cv P a ev p
  ew = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} r ea ev p ev p (≅ᴵ-refl i)

⊑ᴱ-≅ˡ : ∀ {k k′} {x x′ : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x′ → x′ ⊑ᴱ y → x ⊑ᴱ y
⊑ᴱ-≅ˡ e h o G′ = proj₁ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′))) ,
                 ⊑-trans (proj₂ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′)))) (proj₂ (h o G′))
F≅ : ∀ {d flE k k′ i i′ ℓ ℓ′} {E : Fr (suc d) flE} {P : Sp (suc d)} {ev : Ev ℓ (sf P ⊔ (flE ⊔ flo k))} {ev′ : Ev ℓ′ (sf P ⊔ (flE ⊔ flo k′))} {x : Ordˢ k} {y : Ordˢ k′} →
     E ≈U E → P ≈S P → x ≅ˢ y → (p : i <ᴵ ℓ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → fold1 (flo k) (cvFlo k) E x P ev p ≅ˢ fold1 (flo k′) (cvFlo k′) E y P ev′ p′
F≅ {flE = flE} {k = k} {k′ = k′} {ev = ev} {ev′ = ev′} rE r d p p′ ei = fold-≅U {cv = cvFlo k} {cv′ = cvFlo k′} (∼ᶠ-refl flE) rE d r ev p ev′ p′ ei

pfl-of : ∀ {fl} {P : Run fl} → P ≈ᴿ P → (∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ P ev p) → PFl P
pfl-of {P = P} r s1 = pfl r
  (λ {i} ev p → ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (Ωˢ-refl i))) (s1 ev p))
  (λ {φ} {k₂} {j} {ℓ₁} {cv} ev₁ p₁ y ey oy → B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev₁} {p = p₁} r (s1 (proj₁ ev₁) p₁) y ey)

selfRun : ∀ {fl} {P : Run fl} → PFl P → ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → P ev p ≅ˢ P ev p
selfRun pf ev p = PFl.rP pf ev p ev p (≅ᴵ-refl _)

module FramePF {d flE} {E : Fr (suc d) flE} {Q : Sp (suc d)} (fE : FFl E) (pf : SF Q) where
  pfE : PFl (E Q)
  pfE = FFl.pE fE pf

  pfl-F : ∀ {k} {a : Ordˢ k} → a ≅ˢ a → PFl (fold1 (flo k) (cvFlo k) E a Q)
  pfl-F {k} {a} ea = pfl-of (λ ev p ev′ p′ ei → F≅ (FFl.rE fE) (SF≈ pf) ea p p′ ei)
    (λ {i} ev p → B1₁ᴱ {φ = flo k} {E = E} {Q = Q} {cv = cvFlo k} {ev = ev} {p = p} (FFl.s1E fE pf (proj₁ ev , proj₁ (proj₂ ev)) p) a ea)
```

`fflF`: 折叠的帧仍是帧; `flRep`: 帧的副本仍有地板. 按深度分两行, 只有 $d=0$ 与 $d+1$ 的差别.

```agda
fflF : ∀ {d flE k} {E : Fr (suc d) flE} {a : Ordˢ k} → FFl E → a ≅ˢ a → FFl (fold1 (flo k) (cvFlo k) E a)
fflF {flE = flE} {k = k} {E = E} {a = a} fE ea = ffl
  (fold-≅U {cv = cvFlo k} {cv′ = cvFlo k} (∼ᶠ-refl flE) (FFl.rE fE) ea)
  (λ pf → FramePF.pfl-F fE pf ea)
  (λ {Q} pf ev p → B1₁ᴱ {φ = flo k} {E = E} {Q = Q} {cv = cvFlo k} {ev = ev} {p = p} (FFl.s1E fE pf (proj₁ ev , proj₁ (proj₂ ev)) p) a ea)
  (λ {Q} pf ev p → B1₁ᴱ {φ = flo k} {E = E} {Q = Q} {cv = cvFlo k} {ev = ev} {p = p} (FFl.stE fE pf (proj₁ ev , proj₁ (proj₂ ev)) p) a ea)

leHd : ∀ {d flE} {E : Fr (suc d) flE} {Q : Sp (suc d)} → FFl E → SF Q → ∀ {i ℓ} (ev : Ev ℓ (sf Q ⊔ flE)) (p : i <ᴵ ℓ) → proj₁ (proj₂ Q) (proj₂ (proj₂ Q)) (proj₁ ev) p ⊑ᴱ E Q ev p
leHd {Q = Q} fE pf ev p = ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (FlU≈ _ (proj₁ pf) (SF≈ (proj₂ pf)) _ p _ p (≅ᴵ-refl _)))) (FFl.stE fE pf ev p)
```
`flRep`: 帧的副本 (第 $m+1$ 份) 仍有地板, 按深度分两行. `suc-fold₁`: 第 2 份严格高于第 1 份.

```agda
rRep : ∀ {d fl ψ} {P : Fr d fl} {F : Fr (suc d) ψ} → FlU d P → FFl F → ∀ m → repU P F m ≈U repU P F m
rRep {d} {fl} {ψ} hP fF m = repR (∼ᶠ-refl fl) (∼ᶠ-refl ψ) (FlU≈ d hP) (FFl.rE fF) m

flRep : ∀ d {fl ψ} {P : Fr d fl} {F : Fr (suc d) ψ} → FlU d P → FFl F → ∀ m → FlU d (repU P F (suc m))
s1Rep : ∀ d {fl ψ} {P : Fr d fl} {F : Fr (suc d) ψ} → FlU d P → FFl F → ∀ m {s : Sp d} → SF s → ∀ {i ℓ} (ev : Ev ℓ (sf s ⊔ (fl ⊔ ψ))) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ repU P F (suc m) s ev p
s1Rep d hP fF zero    ss ev p = FFl.s1E fF (hP , ss) _ p
s1Rep d hP fF (suc m) ss ev p = FFl.s1E fF (flRep d hP fF m , ss) _ p

stRep : ∀ d {fl ψ} {P : Fr (suc d) fl} {F : Fr (suc (suc d)) ψ} → FlU (suc d) P → FFl F → ∀ m {Q : Sp (suc d)} → SF Q → ∀ {i ℓ} (ev : Ev ℓ (sf Q ⊔ (fl ⊔ ψ))) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (proj₁ (proj₂ Q) (proj₂ (proj₂ Q)) (proj₁ ev) p) ⊑ᴱ repU P F (suc m) Q ev p
stRep d {fl} hP fF zero {Q} pf ev p =
  ⊑ᴱ-trans (FFl.stE hP pf (proj₁ ev , proj₁ (proj₂ ev)) p)
    (⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (FlU≈ (suc d) hP (SF≈ pf) _ p _ p (≅ᴵ-refl _))))
       (FFl.stE fF (hP , pf) ((proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)) p))
stRep d hP fF (suc m) {Q} pf ev p =
  ⊑ᴱ-trans (stRep d hP fF m pf ev p)
    (⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (rRep hP fF (suc m) (SF≈ pf) _ p _ p (≅ᴵ-refl _))))
       (FFl.stE fF (flRep (suc d) hP fF m , pf) (ev , proj₂ (proj₂ ev)) p))

flRep zero hP fF m = pfl-of (rRep hP fF (suc m) tt) (s1Rep zero hP fF m tt)
flRep (suc d) hP fF m = ffl (rRep hP fF (suc m))
  (λ pf → pfl-of (rRep hP fF (suc m) (SF≈ pf)) (s1Rep (suc d) hP fF m pf))
  (λ pf ev p → s1Rep (suc d) hP fF m pf ev p)
  (λ pf ev p → stRep d hP fF m pf ev p)

suc-fold₁ : ∀ {d flE} {E : Fr (suc d) flE} {Q : Sp (suc d)} (fE : FFl E) (pf : SF Q) {k i ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {a : Ordˢ k} → a ≅ˢ a →
            Ord₊ˢ.suc (fold1 (flo k) (cvFlo k) E a Q ev p) ⊑ᴱ fold1 (flo k) (cvFlo k) E (Ord₊ˢ.suc a) Q ev p
suc-fold₁ {d} {flE} {E} {Q} fE pf {k} {ev = ev} {p = p} {a = a} ea =
  lim-rᴱ {h = λ m → rowU Q (fold1 (flo k) (cvFlo k) E a) m ev p} 2
    (B1₁ᴱ {φ = flo k} {E = E} {Q = Q₂} {cv = cvFlo k} {ev = ev₂} {p = p}
        (FFl.stE fE (flRep d (proj₁ pf) (fflF fE ea) 0 , proj₂ pf) (proj₁ ev₂ , proj₁ (proj₂ ev₂)) p) a ea)
  where
  Q₂ : Sp (suc d)
  Q₂ = (proj₁ Q ⊔ (flE ⊔ flo k)) , repU (proj₁ (proj₂ Q)) (fold1 (flo k) (cvFlo k) E a) 1 , proj₂ (proj₂ Q)
  ev₃ : Ev _ (sf (proj₂ (proj₂ Q)) ⊔ (proj₁ Q ⊔ (flE ⊔ flo k)))
  ev₃ = proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)
  ev₂ : Ev _ (sf Q₂ ⊔ (flE ⊔ flo k))
  ev₂ = ev₃ , proj₂ ev
```

## §4 严格增长: 对一切上下文

**`Rs`.** 若 $a+1\sqsubseteq^\mathsf Ey$, 则对一切上下文, $y$ 一侧的证书给出 $a$ 一侧的证书, 计值严格 $\prec$. 每过一个折叠, $+1$ 由 `suc-fold` 再生 ($\psi(a+1)=\psi(a)\cdot\omega\ni\psi(a)+1$); 加法定义性交换. 这是 Growth §3 的上下文无关形式: 栈的长度与前缀的阶段都不进证明.

```agda
Rs : ∀ {k k′} {a : Ordˢ k} {y : Ordˢ k′} → a ≅ˢ a → Ord₊ˢ.suc a ⊑ᴱ y →
    ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → Ctx O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
    Σ (Goodᴺ (toZ (run O a))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Rs ea sa idO c G′ with sa idO G′
... | gs Ga , h = Ga , h (≺z (≅-refl⁰ _))
Rs {a = a} {y = y} ea sa (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) (pf , c) G′ =
  Rs {a = fold 0 φ cv P a ev p} {y = fold 0 φ′ cv′ P y ev′ p′}
    (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} r ea ev p ev p (≅ᴵ-refl _))
    (⊑ᴱ-trans (suc-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {a = a} r (PFl.f0 pf) ea)
              (fold-congᴱ {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} r sa))
    o c G′
Rs {a = a} {y = y} ea sa (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) (fE , pf , c) G′ =
  Rs {a = fold1 (flo K₁) (cvFlo K₁) E a P ev p} {y = fold1 (flo K₁′) (cvFlo K₁′) E y P ev′ p′}
    (F≅ rE r ea p p (≅ᴵ-refl _))
    (⊑ᴱ-trans (suc-fold₁ fE pf {ev = ev} {p = p} {a = a} ea) (fold1-congᴱ rE r sa))
    o c G′
Rs {a = a} {y = y} ea sa (addo {a = e} {a′ = e′} {σ = σ} {σ′ = σ′} o k ee) (_ , c) G′ =
  Rs {a = addˢ e σ a} {y = addˢ e′ σ′ y} (addˢ-≅ (≅ᴵ-refl _) (≅ˢ-reflˡ ee) ea)
    (add-congᴱ {a = e} {a′ = e′} {σ = σ} {σ′ = σ′} {x = Ord₊ˢ.suc a} {y = y} k ee sa) o c G′
Rs {a = a} {y = y} ea sa (tro {e = e} {e′ = e′} o) c G′ =
  Rs {a = trˢ e a} {y = trˢ e′ y} (self-trˢ e ea) (tr-congᴱ {e = e} {e′ = e′} {x = Ord₊ˢ.suc a} {y = y} sa) o c G′
Rs {a = a} {y = y} ea sa (tr⁻o {e = e} {e′ = e′} o) c G′ =
  Rs {a = tr⁻ˢ e a} {y = tr⁻ˢ e′ y} (self-tr⁻ˢ e ea) (tr⁻-congᴱ {e = e} {e′ = e′} {x = Ord₊ˢ.suc a} {y = y} sa) o c G′
```

**`Climb`.** 对节点 $j$ 的 `limᵢ q f`: 若 "$z\sqsupseteq^\mathsf E\Omega_j+1$ 推出 $x+1\sqsubseteq^\mathsf Ef\,z$", 则 $x$ 严格低于 `limᵢ q f`, 对一切上下文. 穿透的折叠与加法把假设搬到输出分支上; 第一个折叠节点 $j$ 的上下文头 (目标 $\preceq j$) 取链的第 1 点 $z_1=\mathrm{fold}_j(f\,\Omega_j)$, 它由 `fS` 满足前提, 再由 `Rs` 走完剩下的栈. `rf` 代替 `limᵢ` 的自互模拟 (在 `with` 分支里 `fold-≅0` 的结果类型不归约).

```agda
back-sucᴱ : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (resˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (resˢ q e) u
back-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} h)
back-sucᴱ (suc q)   (s≅ e) eu h = back-sucᴱ q e eu h
back-sucᴱ (lim n q) (l≅ f) eu h = back-sucᴱ q (f n) eu h

back⁻-sucᴱ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (res⁻ˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (res⁻ˢ q e) u
back⁻-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = trˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (trˢ-≅ e (Ωˢ-≅ e)))) (tr-congᴱ {e = e} {e′ = e} h)
back⁻-sucᴱ (suc q)   (s≅ e) eu h = back⁻-sucᴱ q e eu h
back⁻-sucᴱ (lim n q) (l≅ f) eu h = back⁻-sucᴱ q (f n) eu h

chainC : ∀ {fl φ φ′ k k₀ j i ℓ ℓ′} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k₀ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k L}
         {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {x : Ordˢ k₀} →
         x ≅ˢ x → (∀ {z z′} → z ≅ˢ z′ → f (intoˢ (<→◃ q) z) ≅ˢ f (intoˢ (<→◃ q) z′)) →
         (∀ z → z ≅ˢ Ωˢ j → 𝟏 ⊑ᴱ f (intoˢ (<→◃ q) z)) →
         (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → Ord₊ˢ.suc x ⊑ᴱ f (intoˢ (<→◃ q) z)) →
         ∀ {O O′ : Obs i} → O ≈ᵒ O′ → P ≈ᴿ P → PFl P → Ctx O′ →
         (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.lim (λ m → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (iter (λ w → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) w)) ev′ (cv′ (proj₂ ev′) q)) (Ωˢ j) m))) ev′ p′))))) →
         Σ (Goodᴺ (toZ (run O (fold 0 φ cv P x ev p)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
chainC {φ = φ} {φ′ = φ′} {j = j} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h1 h2 {O} {O′} o r pf c G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  ef : f (intoˢ (<→◃ q) (Ωˢ j)) ≅ˢ f (intoˢ (<→◃ q) (Ωˢ j))
  ef = rf (Ωˢ-refl j)
  z₁ = fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (Ωˢ j))) ev′ (cv′ (proj₂ ev′) q)
  ez₁ : z₁ ≅ˢ z₁
  ez₁ = fold-≅0 {φ = φ′} {φ′ = φ′} {cv = cv′} {cv′ = cv′} {P = P} {P′ = P} r ef ev′ _ ev′ _ (≅ᴵ-refl _)
  sz₁ : Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z₁
  sz₁ = PFl.fS pf {φ = φ′} {cv = cv′} ev′ (cv′ (proj₂ ev′) q) (f (intoˢ (<→◃ q) (Ωˢ j))) ef (h1 _ (Ωˢ-refl j))
  y₁ = fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) z₁)) ev′ p′
  ey₁ : y₁ ≅ˢ y₁
  ey₁ = fold-≅0 {φ = φ′} {φ′ = φ′} {cv = cv′} {cv′ = cv′} {P = P} {P′ = P} r (rf ez₁) ev′ _ ev′ _ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ m → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (iter (λ w → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) w)) ev′ (cv′ (proj₂ ev′) q)) (Ωˢ j) m))) ev′ p′}
             1 (≅→⊑ᴱ {x = y₁} ey₁) (≈ᵒ-reflʳ o) G′
  S = Rs {a = x} {y = f (intoˢ (<→◃ q) z₁)} ex (h2 z₁ ez₁ sz₁) (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) (pf , c) (proj₁ L)

chainC₁ : ∀ {d flE K₁ K₁′ j i ℓ ℓ′} {E : Fr (suc d) flE} {P : Sp (suc d)}
          {ev : Ev ℓ (sf P ⊔ (flE ⊔ flo K₁))} {ev′ : Ev ℓ′ (sf P ⊔ (flE ⊔ flo K₁′))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {q : j <ᴵ K₁′} {f : Uˢ j (<→◃ q) → Ordˢ K₁′} {x : Ordˢ K₁} →
         x ≅ˢ x → (∀ {z z′} → z ≅ˢ z′ → f (intoˢ (<→◃ q) z) ≅ˢ f (intoˢ (<→◃ q) z′)) →
         (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → Ord₊ˢ.suc x ⊑ᴱ f (intoˢ (<→◃ q) z)) →
         ∀ {O O′ : Obs i} → O ≈ᵒ O′ → E ≈U E → P ≈S P → FFl E → SF P → Ctx O′ →
         (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.lim (λ m → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (iter (λ w → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) w)) P ev′ (cvFlo K₁′ (proj₂ (proj₂ ev′)) q)) (Ωˢ j) m))) P ev′ p′))))) →
         Σ (Goodᴺ (toZ (run O (fold1 (flo K₁) (cvFlo K₁) E x P ev p)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
chainC₁ {K₁ = K₁} {K₁′ = K₁′} {j = j} {E = E} {P = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h2 {O} {O′} o rE r fE pf c G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  ef : f (intoˢ (<→◃ q) (Ωˢ j)) ≅ˢ f (intoˢ (<→◃ q) (Ωˢ j))
  ef = rf (Ωˢ-refl j)
  ac = cvFlo K₁′ (proj₂ (proj₂ ev′)) q
  z₁ = fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (Ωˢ j))) P ev′ ac
  ez₁ : z₁ ≅ˢ z₁
  ez₁ = F≅ {ev = ev′} {ev′ = ev′} rE r ef ac ac (≅ᴵ-refl _)
  sz₁ : Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z₁
  sz₁ = B1₁ᴱ {φ = flo K₁′} {E = E} {Q = P} {cv = cvFlo K₁′} {ev = ev′} {p = ac} (FFl.s1E fE pf (proj₁ ev′ , proj₁ (proj₂ ev′)) ac) (f (intoˢ (<→◃ q) (Ωˢ j))) ef
  y₁ = fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) z₁)) P ev′ p′
  ey₁ : y₁ ≅ˢ y₁
  ey₁ = F≅ {ev = ev′} {ev′ = ev′} rE r (rf ez₁) p′ p′ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ m → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (iter (λ w → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) w)) P ev′ ac) (Ωˢ j) m))) P ev′ p′}
             1 (≅→⊑ᴱ {x = y₁} ey₁) (≈ᵒ-reflʳ o) G′
  S = Rs {a = x} {y = f (intoˢ (<→◃ q) z₁)} ex (h2 z₁ ez₁ sz₁) (fo1 {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) (fE , pf , c) (proj₁ L)

Climb : ∀ {k k₀ j} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {x : Ordˢ k₀} → x ≅ˢ x →
        (∀ {z z′} → z ≅ˢ z′ → f (intoˢ (<→◃ q) z) ≅ˢ f (intoˢ (<→◃ q) z′)) →
        (∀ z → z ≅ˢ Ωˢ j → 𝟏 ⊑ᴱ f (intoˢ (<→◃ q) z)) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → Ord₊ˢ.suc x ⊑ᴱ f (intoˢ (<→◃ q) z)) →
        ∀ {O : Obs k₀} {O′ : Obs k} → O ≈ᵒ O′ → Ctx O′ → (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.limᵢ q f)))) →
        Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Climb {q = ()} ex rf h1 h2 idO c G′
Climb {j = j} {q = q} {f = f} {x = x} ex rf h1 h2
      (fo {i = i} {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) (pf , c) G′
  with <ᴵ-dec (cv′ (proj₂ ev′) q) p′
... | injᵃ (via e s) =
  Climb {q = s} {f = λ u → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ s) u)))) ev′ p′} {x = fold 0 φ cv P x ev p}
    (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} r ex ev p ev p (≅ᴵ-refl _))
    (λ {z} {z′} d → subst₂ (λ u v → fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′ ≅ˢ fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev′ p′)
                           (sym (out-intoˢ (<→◃ s) z)) (sym (out-intoˢ (<→◃ s) z′))
                           (fold-≅0 {φ = φ′} {φ′ = φ′} {cv = cv′} {cv′ = cv′} {P = P} {P′ = P} r (rf (tr⁻ˢ-≅ e (≅-tr⁻ˢ e d))) ev′ p′ ev′ p′ (≅ᴵ-refl _)))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (B1ᴱ {φ = φ′} {P = P} {cv = cv′} {ev = ev′} {p = p′} {x = 𝟏} r (⊑ᴱ-trans (Ω1ᴱ i) (PFl.f0 pf (proj₁ ev′) p′)) _
                        (rf (self-tr⁻ˢ e (≅ˢ-reflˡ d)))))
    (λ z ez sz → subst (λ u → Ord₊ˢ.suc (fold 0 φ cv P x ev p) ⊑ᴱ fold 0 φ′ cv′ P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (⊑ᴱ-trans (suc-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {a = x} r (PFl.f0 pf) ex)
                             (fold-congᴱ {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} r
                               (h2 (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                                   (⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} sz))))))
    o c G′
... | injᵇ _ = chainC {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h1 h2 o r pf c G′
... | injᶜ _ = chainC {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h1 h2 o r pf c G′
Climb {j = j} {q = q} {f = f} {x = x} ex rf h1 h2
      (fo1 {i = i} {k = K₁} {k′ = K₁′} {E = E} {Q = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o rE r) (fE , pf , c) G′
  with <ᴵ-dec (cvFlo K₁′ (proj₂ (proj₂ ev′)) q) p′
... | injᵃ (via e s) =
  Climb {q = s} {f = λ u → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ s) u)))) P ev′ p′} {x = fold1 (flo K₁) (cvFlo K₁) E x P ev p}
    (F≅ {k = K₁} {k′ = K₁} {E = E} {P = P} {ev = ev} {ev′ = ev} rE r ex p p (≅ᴵ-refl _))
    (λ {z} {z′} d → subst₂ (λ u v → fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) P ev′ p′ ≅ˢ fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) P ev′ p′)
                           (sym (out-intoˢ (<→◃ s) z)) (sym (out-intoˢ (<→◃ s) z′))
                           (F≅ {k = K₁′} {k′ = K₁′} {E = E} {P = P} {ev = ev′} {ev′ = ev′} rE r (rf (tr⁻ˢ-≅ e (≅-tr⁻ˢ e d))) p′ p′ (≅ᴵ-refl _)))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) P ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (B1₁ᴱ {φ = flo K₁′} {E = E} {Q = P} {cv = cvFlo K₁′} {ev = ev′} {p = p′} {x = 𝟏} (⊑ᴱ-trans (Ω1ᴱ i) (PFl.f0 (FFl.pE fE pf) (proj₁ ev′ , proj₁ (proj₂ ev′)) p′)) _
                        (rf (self-tr⁻ˢ e (≅ˢ-reflˡ d)))))
    (λ z ez sz → subst (λ u → Ord₊ˢ.suc (fold1 (flo K₁) (cvFlo K₁) E x P ev p) ⊑ᴱ fold1 (flo K₁′) (cvFlo K₁′) E (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) P ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (⊑ᴱ-trans (suc-fold₁ fE pf {ev = ev} {p = p} {a = x} ex)
                             (fold1-congᴱ {E = E} {P = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} rE r
                               (h2 (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                                   (⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} sz))))))
    o c G′
... | injᵇ _ = chainC₁ {E = E} {P = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h2 o rE r fE pf c G′
... | injᶜ _ = chainC₁ {E = E} {P = P} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {q = q} {f = f} {x = x} ex rf h2 o rE r fE pf c G′
Climb {k = k} {j = j} {q = q} {f = f} {x = x} ex rf h1 h2 (addo {a = e} {a′ = e′} {σ = σ} {σ′ = σ′} o kk ee) (afl e₁ one , c) G′ =
  Climb {q = σ′ q} {f = λ u → addˢ e′ σ′ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ′ q)) u)))} {x = addˢ e σ x}
    (addˢ-≅ (≅ᴵ-refl _) (≅ˢ-reflˡ ee) ex)
    (λ {z} {z′} d → subst₂ (λ u v → addˢ e′ σ′ (f (intoˢ (<→◃ q) u)) ≅ˢ addˢ e′ σ′ (f (intoˢ (<→◃ q) v)))
                           (sym (out-intoˢ (<→◃ (σ′ q)) z)) (sym (out-intoˢ (<→◃ (σ′ q)) z′)) (addˢ-≅ (≅ᴵ-refl _) e₁ (rf d)))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ addˢ e′ σ′ (f (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
                   (add-floorᴱ {σ = σ′} (f (intoˢ (<→◃ q) z)) one (rf (≅ˢ-reflˡ d))))
    (λ z ez sz → subst (λ u → Ord₊ˢ.suc (addˢ e σ x) ⊑ᴱ addˢ e′ σ′ (f (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
                       (add-congᴱ {a = e} {a′ = e′} {σ = σ} {σ′ = σ′} {x = Ord₊ˢ.suc x} {y = f (intoˢ (<→◃ q) z)} kk ee (h2 z ez sz)))
    o c G′
Climb {k = k} {q = q} {f = f} {x = x} ex rf h1 h2 (tro {e = e₀} {e′ = e} o) c G′ =
  Climb {q = ltˢ (resˢ q e)} {f = λ u → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) u))))} {x = trˢ e₀ x}
    (self-trˢ e₀ ex)
    (λ {z} {z′} d → subst₂ (λ u v → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))) ≅ˢ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v))))
       (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′)) (trˢ-≅ e (≅-trˢ e (rf (≅ˢ-trans (backˢ-≅ q e d) (≅ˢ-sym (backˢ-≅ q e (≅ˢ-reflʳ d))))))))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (tr-congᴱ {e = z≅} {e′ = e} (h1 _ (≅ˢ-trans (backˢ-≅ q e d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e))))))))
    (λ z ez sz → subst (λ u → Ord₊ˢ.suc (trˢ e₀ x) ⊑ᴱ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (tr-congᴱ {e = e₀} {e′ = e} {x = Ord₊ˢ.suc x} (h2 _ (≅ˢ-reflˡ (backˢ-≅ q e ez)) (back-sucᴱ q e ez sz))))
    o c G′
Climb {k = k} {q = q} {f = f} {x = x} ex rf h1 h2 (tr⁻o {e = e₀} {e′ = e} o) c G′ =
  Climb {q = ltˢ (res⁻ˢ q e)} {f = λ u → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))))} {x = tr⁻ˢ e₀ x}
    (self-tr⁻ˢ e₀ ex)
    (λ {z} {z′} d → subst₂ (λ u v → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))) ≅ˢ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v))))
       (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)) (tr⁻ˢ-≅ e (≅-tr⁻ˢ e (rf (≅ˢ-trans (back⁻ˢ-≅ q e d) (≅ˢ-sym (back⁻ˢ-≅ q e (≅ˢ-reflʳ d))))))))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (tr⁻-congᴱ {e = z≅} {e′ = e} (h1 _ (≅ˢ-trans (back⁻ˢ-≅ q e d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e))))))))
    (λ z ez sz → subst (λ u → Ord₊ˢ.suc (tr⁻ˢ e₀ x) ⊑ᴱ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (tr⁻-congᴱ {e = e₀} {e′ = e} {x = Ord₊ˢ.suc x} (h2 _ (≅ˢ-reflˡ (back⁻ˢ-≅ q e ez)) (back⁻-sucᴱ q e ez sz))))
    o c G′
```

## §5 $\Omega_j\prec\Omega_{j+1}$, 对一切上下文

```agda
Ω-strict : ∀ j {O : Obs j} {O′ : Obs (suc j)} → O ≈ᵒ O′ → Ctx O′ → (G′ : Goodᴺ (toZ (run O′ (Ωˢ (suc j))))) →
           Σ (Goodᴺ (toZ (run O (Ωˢ j)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Ω-strict j = Climb {q = zero} {f = Ord₊ˢ.up zero} {x = Ωˢ j} (Ωˢ-refl j) (λ d → upˡ {r = zero} (upʳ {r = zero} d))
                   (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ j) (≅ˢ-sym d)))
                   (λ z ez sz → up-rᴱ {r = zero} {y = z} sz)

Ω<ᴱ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᴱ Ωˢ b
Ω<ᴱ e zero      = ≅→⊑ᴱ (Ωˢ-≅ (s≅ e))
Ω<ᴱ e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω<ᴱ e q) (≅ˢ-sym d)))
Ω<ᴱ e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (Ω<ᴱ e q))
```

## §6 前缀的地板: 空前缀与 $\Omega_\Omega$ 闭包

`pfl∅`, **`pfl-Ω̂ : PFl Q → PFl (Ω̂A 0 Q)`**: 一条阶段步, 没有任何支配前提. 闭包的第 0 点 `fold (fk zero) (λ e → e) Q Ω₁` 经 `ŝ-rᴱ` 给出闭包的地板, 与闭包的界无关. 这里只读 `cloA` 的第 0 点, 不读 `fk`/`flo` 的具体形状.

```agda
pfl∅ : PFl ∅ᴿ
pfl∅ = pfl r∅ (λ {i} ev p → ≅→⊑ᴱ (Ωˢ-refl i)) fS∅
  where
  fS∅ : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ (fz ⊔ φ)) (p : i <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y →
        𝟏 ⊑ᴱ y → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ fold 0 φ cv ∅ᴿ y ev p
  fS∅ {φ = φ} {i = i} {cv = cv} ev p y ey h =
    ⊑ᴱ-trans (suc-fold {φ = fz} {P = ∅ᴿ} {cv = λ _ → σ₀} {ev = proj₁ ev , tt} {p = p} {a = Ord₊ˢ.zero} r∅ (λ {i′} ev′ p′ → ≅→⊑ᴱ (Ωˢ-refl i′)) z≅)
             (fold-congᴱ {φ = fz} {φ′ = φ} {P = ∅ᴿ} {cv = λ _ → σ₀} {cv′ = cv} {ev = proj₁ ev , tt} {ev′ = ev} {p = p} {p′ = p} r∅ h)

pfl-Ω̂ : ∀ {fl} {Q : Run fl} → PFl Q → PFl (Ω̂A 0 Q)
pfl-Ω̂ {fl} {Q} (pfl r f0 fS) = pfl (rΩ̂ r) f0′ fS′
  where
  Ω₁ = Ωˢ (suc zero)
  eΩ₁ = Ωˢ-refl (suc zero)
  f0′ : ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ fk zero)) (p : i <ᴵ ℓ) → Ωˢ i ⊑ᴱ Ω̂A 0 Q ev p
  f0′ {i} ev p = ŝ-rᴱ (B1ᴱ {φ = fk zero} {P = Q} {cv = λ e → e} {ev = ev} {p = p} {x = Ωˢ i} r (f0 (proj₁ ev) p) Ω₁ eΩ₁)
  fS′ : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ ((fl ⊔ fk zero) ⊔ φ)) (p : i <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y →
        𝟏 ⊑ᴱ y → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ fold 0 φ cv (Ω̂A 0 Q) y ev p
  fS′ {φ = φ} {i = i} {cv = cv} ev p y ey h =
    B1ᴱ {φ = φ} {P = Ω̂A 0 Q} {cv = cv} {ev = ev} {p = p} {x = Ord₊ˢ.suc (Ωˢ i)} (rΩ̂ r)
        (ŝ-rᴱ (fS {φ = fk zero} {cv = λ e → e} (proj₁ ev) p Ω₁ eΩ₁ (Ω1ᴱ (suc zero)))) y ey
```

