# 无记号主线 (十一): 闭包类

> **`Good`, 类 `Cl`, 可见性 `Vis`, 判据 `Hon`, 外层 `bŝ`, 以及出口 `Good→N : Good s 𝓖 x → Goodᴺ (toZ x)`.**
> 脚本从 [UniformNF5Class](../Align/UniformNF5Class.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; Restrˢ; resˢ; res⁻ˢ)
open import OCF.Free.Eq using (⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; toZ-≅; Ωˢ-≅; Ωˢ-refl; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; self-trˢ; self-tr⁻ˢ; ĉ-refl₀; ĉ-reflg; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; backˢ-≅; back⁻ˢ-≅; addˢ-≅)
open import OCF.Free.Floor using (flo; cvFlo; toFlo; Ev)
open import OCF.Free.Aux using (one⁰)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Force using (Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Base
open import OCF.Free.Rules
open import OCF.Free.Strict
```

```agda
open Ord-Ord using (iter)
open Restrˢ
open RestrO
```

## §0 观测前序

```agda
infix 4 _⊑ᵒ_ _⊑ᵗ_
_⊑ᵒ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ →
  (G : Goodᴺ (toZ (run O x))) (G′ : Goodᴺ (toZ (run O′ y))) → forceᴺ _ G ⊑ forceᴺ _ G′

_⊑ᵗ_ : ∀ {c φ ψ} → O c φ → O c ψ → Set
_⊑ᵗ_ {c} {φ} {ψ} x y = ∀ {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ →
  (G : Goodᴺ (toZ (runᶜ C x))) (G′ : Goodᴺ (toZ (runᶜ C′ y))) → forceᴺ _ G ⊑ forceᴺ _ G′

pull≅ : ∀ {u v : Ordˢ zero} → u ≡ v → (G′ : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G → (forceᴺ _ G ⊑ forceᴺ _ G′) × (forceᴺ _ G′ ⊑ forceᴺ _ G)
pull≅ refl G′ = G′ , (λ h → h) , (λ h → h)

⊑ᴱ→ᵒ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x → x ⊑ᴱ y → x ⊑ᵒ y
⊑ᴱ→ᵒ ex h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (run-≅ (≈ᵒ-reflˡ o) ex)) G (proj₁ (h o G′)))) (proj₂ (h o G′))

⊑ᵀ→ᵗ : ∀ {c φ ψ} {x : O c φ} {y : O c ψ} → Rᵒ c c x x → x ⊑ᵀ y → x ⊑ᵗ y
⊑ᵀ→ᵗ ex h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) ex)) G (proj₁ (h o G′)))) (proj₂ (h o G′))

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → x ⊑ᵒ y → addˢ a σ x ⊑ᵒ addˢ a′ σ′ y
add-cong k e h o = h (addo o k e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᵒ y → trˢ e x ⊑ᵒ trˢ e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᵒ y → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ y
tr⁻-cong h o = h (tr⁻o o)

ψ̄-congᵒ : ∀ {c φ ψ i ℓ ℓ′} {x : O c φ} {y : O c ψ} {ev : Ev ℓ φ} {ev′ : Ev ℓ′ ψ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} → x ⊑ᵗ y → ψ̄ x ev p ⊑ᵒ ψ̄ y ev′ p′
ψ̄-congᵒ h o = h (top o)

tl-congᵒ : ∀ {c k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᵒ y → tl {c = c} (flo k) (cvFlo k) x ⊑ᵗ tl {c = c} (flo k′) (cvFlo k′) y
tl-congᵒ h o = h (tlo o)

⊕-congᵗ : ∀ {c a φ ψ} {W : O c a} {x : O c φ} {y : O c ψ} → Rᵒ c c W W → x ⊑ᵗ y → W ⊕ x ⊑ᵗ W ⊕ y
⊕-congᵗ r h o = h (pa r o)

ψ-congᵗ : ∀ {c t φ ψ} {q : t <ᴵ c} {x : O c φ} {y : O c ψ} → x ⊑ᵗ y → ψᵒ q x ⊑ᵗ ψᵒ q y
ψ-congᵗ {q = q} h o = h (pψ {q = q} o)

ι-congᵗ : ∀ {c d φ ψ} {q : c ◃ d} {x : O c φ} {y : O c ψ} → x ⊑ᵗ y → ι q x ⊑ᵗ ι q y
ι-congᵗ {q = q} h o = h (pι {q = q} o)

trᵗ-cong : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {x : O a φ} {y : O a ψ} → x ⊑ᵗ y → trO e x ⊑ᵗ trO e′ y
trᵗ-cong h o = h (ptr o)

tr⁻ᵗ-cong : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {x : O b φ} {y : O b ψ} → x ⊑ᵗ y → tr⁻O e x ⊑ᵗ tr⁻O e′ y
tr⁻ᵗ-cong h o = h (ptr⁻ o)

wk-lᵗ : ∀ {c φ φ′ ψ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {x : O c φ} {y : O c ψ} → x ⊑ᵗ y → owk le x ⊑ᵗ y
wk-lᵗ {le = le} {x = x} h {C} o G G′ = ⊑-trans (proj₂ (proj₂ J)) (h (≈ᶜ-wkˡ le o) (proj₁ J) G′)
  where J = pull≅ (run-wkC le C x) G

wk-rᵗ : ∀ {c χ φ ψ} {le : ∀ {L} → Ev L ψ → Ev L φ} {x : O c χ} {y : O c φ} → x ⊑ᵗ y → x ⊑ᵗ owk le y
wk-rᵗ {le = le} {y = y} h {C′ = C′} o G G′ = ⊑-trans (h (≈ᶜ-wkʳ le o) G (proj₁ J)) (proj₁ (proj₂ J))
  where J = pull≅ (run-wkC le C′ y) G′

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᵒ y → Ord₊ˢ.up r x ⊑ᵒ y
up-l {k = k} {r = zero} {x = x} h (tlo o) = wk-lᵗ {x = tl (flo k) (cvFlo k) x} (tl-congᵒ h) o
up-l {k = k} {r = self n} {x = x} h (tlo o) = wk-lᵗ {x = tl (flo k) (cvFlo k) x} (tl-congᵒ h) o
up-l {r = zero}   h (addo o k e) = h (addo o k e)
up-l {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-l {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-l {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (addo o k e) = h (addo o k e)
up-l {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-l {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-l {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᵒ outˢ (◃₁→◃ r) y → x ⊑ᵒ Ord₊ˢ.up r y
up-r {k = k} {r = zero} {y = y} h (tlo o) = wk-rᵗ {y = tl (flo k) (cvFlo k) y} (tl-congᵒ h) o
up-r {k = k} {r = self n} {y = y} h (tlo o) = wk-rᵗ {y = tl (flo k) (cvFlo k) y} (tl-congᵒ h) o
up-r {r = zero}   h (addo o k e) = h (addo o k e)
up-r {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-r {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-r {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (addo o k e) = h (addo o k e)
up-r {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-r {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-r {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o

lim-l : ∀ {k k′} {h : ℕ → Ordˢ k} {y : Ordˢ k′} → (∀ n → h n ⊑ᵒ y) → Ord₊ˢ.lim h ⊑ᵒ y
lim-lᵗ : ∀ {c φ ψ} {F : ℕ → O c φ} {y : O c ψ} → (∀ n → F n ⊑ᵗ y) → ol F ⊑ᵗ y
lim-l K idO (gl G st) G′ = lim-⊑ (λ n → K n idO (G n) G′)
lim-l {k = k} {k′ = k′} {h = h} {y = y} K (tlo o) =
  lim-lᵗ {F = λ m → tl (flo k) (cvFlo k) (h m)} {y = tl (flo k′) (cvFlo k′) y} (λ n o′ → K n (tlo o′)) o
lim-l {h = h} {y = y} K (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) =
  lim-l {h = λ m → addˢ a σ (h m)} {y = addˢ a′ σ′ y} (λ n o′ → K n (addo o′ k ea)) o
lim-l {h = h} {y = y} K (tro {e = e} {e′ = e′} o)  =
  lim-l {h = λ m → trˢ e (h m)} {y = trˢ e′ y} (λ n o′ → K n (tro o′)) o
lim-l {h = h} {y = y} K (tr⁻o {e = e} {e′ = e′} o) =
  lim-l {h = λ m → tr⁻ˢ e (h m)} {y = tr⁻ˢ e′ y} (λ n o′ → K n (tr⁻o o′)) o
lim-lᵗ {F = F} {y = y} K (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) =
  lim-l {h = λ m → ψ̄ (F m) ev p} {y = ψ̄ y ev′ p′} (λ n o′ → K n (top o′)) o
lim-lᵗ {F = F} {y = y} K (pa {W = W} r o) = lim-lᵗ {F = λ m → W ⊕ F m} {y = W ⊕ y} (λ n o′ → K n (pa r o′)) o
lim-lᵗ {F = F} {y = y} K (pψ {q = q} o) = lim-lᵗ {F = λ m → ψᵒ q (F m)} {y = ψᵒ q y} (λ n o′ → K n (pψ {q = q} o′)) o
lim-lᵗ {F = F} {y = y} K (pι {q = q} o) = lim-lᵗ {F = λ m → ι q (F m)} {y = ι q y} (λ n o′ → K n (pι {q = q} o′)) o
lim-lᵗ {F = F} {y = y} K (ptr {e = e} {e′ = e′} o) = lim-lᵗ {F = λ m → trO e (F m)} {y = trO e′ y} (λ n o′ → K n (ptr {e = e} {e′ = e′} o′)) o
lim-lᵗ {F = F} {y = y} K (ptr⁻ {e = e} {e′ = e′} o) = lim-lᵗ {F = λ m → tr⁻O e (F m)} {y = tr⁻O e′ y} (λ n o′ → K n (ptr⁻ {e = e} {e′ = e′} o′)) o

Ω0ᵒ : ∀ b → Ωˢ zero ⊑ᵒ Ωˢ b
Ω0ᵒ b = ⊑ᴱ→ᵒ (Ωˢ-refl zero) (Ω0ᴱ b)

Ω<ᵒ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᵒ Ωˢ b
Ω<ᵒ {a} e q = ⊑ᴱ→ᵒ (Ωˢ-refl (suc a)) (Ω<ᴱ e q)

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ωˢ a ⊑ᵒ Ωˢ b
Ω-monoᵒ {b = b} z⊑ = Ω0ᵒ b
Ω-monoᵒ (s⊑ e q)   = Ω<ᵒ e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l {r = self n} (Ω-monoᵒ (k n)))

rule4ᵒ : ∀ {ℓ} {c : Ordˢ ℓ} → c ≅ˢ c → ∀ n → iter (c +ˢ_) Ord₊ˢ.zero n ⊑ᵒ iter (c +ˢ_) Ord₊ˢ.zero (suc n)
rule4ᵒ {ℓ} {c} ec zero    = ⊑ᴱ→ᵒ z≅ (zero-lᴱ ec)
rule4ᵒ ec (suc n) = add-cong (≅ᴵ-refl _) ec (rule4ᵒ ec n)

≈ᶜ-sym : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → C′ ≈ᶜ C
≈ᵒ-sym′ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O
≈ᵒ-sym′ idO = idO
≈ᵒ-sym′ (tlo o) = tlo (≈ᶜ-sym o)
≈ᵒ-sym′ (addo o k e) = addo (≈ᵒ-sym′ o) (≅ᴵ-sym k) (≅ˢ-sym e)
≈ᵒ-sym′ (tro o) = tro (≈ᵒ-sym′ o)
≈ᵒ-sym′ (tr⁻o o) = tr⁻o (≈ᵒ-sym′ o)
≈ᶜ-sym (top o) = top (≈ᵒ-sym′ o)
≈ᶜ-sym (pa r o) = pa r (≈ᶜ-sym o)
≈ᶜ-sym (pψ o) = pψ (≈ᶜ-sym o)
≈ᶜ-sym (pι o) = pι (≈ᶜ-sym o)
≈ᶜ-sym (ptr o) = ptr (≈ᶜ-sym o)
≈ᶜ-sym (ptr⁻ o) = ptr⁻ (≈ᶜ-sym o)

≈ᶜ-trans : ∀ {c φ ψ χ} {C : Cx c φ} {C′ : Cx c ψ} {C″ : Cx c χ} → C ≈ᶜ C′ → C′ ≈ᶜ C″ → C ≈ᶜ C″
≈ᵒ-trans′ : ∀ {k k′ k″} {O : Obs k} {O′ : Obs k′} {O″ : Obs k″} → O ≈ᵒ O′ → O′ ≈ᵒ O″ → O ≈ᵒ O″
≈ᵒ-trans′ idO idO = idO
≈ᵒ-trans′ (tlo o) (tlo o′) = tlo (≈ᶜ-trans o o′)
≈ᵒ-trans′ (addo o k e) (addo o′ k′ e′) = addo (≈ᵒ-trans′ o o′) (≅ᴵ-trans k k′) (≅ˢ-trans e e′)
≈ᵒ-trans′ (tro o) (tro o′) = tro (≈ᵒ-trans′ o o′)
≈ᵒ-trans′ (tr⁻o o) (tr⁻o o′) = tr⁻o (≈ᵒ-trans′ o o′)
≈ᶜ-trans (top o) (top o′) = top (≈ᵒ-trans′ o o′)
≈ᶜ-trans (pa r o) (pa _ o′) = pa r (≈ᶜ-trans o o′)
≈ᶜ-trans (pψ o) (pψ o′) = pψ (≈ᶜ-trans o o′)
≈ᶜ-trans (pι o) (pι o′) = pι (≈ᶜ-trans o o′)
≈ᶜ-trans (ptr o) (ptr o′) = ptr (≈ᶜ-trans o o′)
≈ᶜ-trans (ptr⁻ o) (ptr⁻ o′) = ptr⁻ (≈ᶜ-trans o o′)

Ctx-wkC : ∀ {c φ ψ} {le : ∀ {L} → Ev L ψ → Ev L φ} (C : Cx c ψ) → Ctxᶜ C → Ctxᶜ (wkC le C)
Ctx-wkC (top O ev p) c = c
Ctx-wkC (pa W C) (w , c) = w , Ctx-wkC C c
Ctx-wkC (pψ q C) c = Ctx-wkC C c
Ctx-wkC (pι q C) c = Ctx-wkC C c
Ctx-wkC (ptr e C) c = Ctx-wkC C c
Ctx-wkC (ptr⁻ e C) c = Ctx-wkC C c
```

## §1 上下文类

```agda
Cl : Ordᴵ → Set₁
Cl ℓ = Obs ℓ → Set

lvG : ∀ {x : Z} → Goodᴺ x → Ordᴵ
lvG G = toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

FlΩ : ∀ {k} → Ordᴵ → Ordˢ k → Set
FlΩ b t = ∀ {k₀} {x : Ordˢ k₀} → x ≅ˢ x → x ⊑ᴱ Ωˢ b → x ⊑ᴱ t

CvP : ∀ {k} → Obs k → Ordᴵ → Set
CvP {k} C b = (t : Ordˢ k) → t ≅ˢ t → FlΩ b t → (G : Goodᴺ (toZ (run C t))) → suc b ⊑ᴵ lvG G

Hon : ∀ (ℓ : Ordᴵ) → Ordˢ ℓ → Obs ℓ → Set
Hon ℓ a C = (G : Goodᴺ (toZ (run C a))) → ℓ ⊑ᴵ lvG G

record Vis (K : Ordᴵ) {k} (C : Obs k) : Set where
  constructor vis
  field
    cx : Ctx C
    cp : ∀ {b} → b ≺ᴵ K → CvP C b
open Vis public

isId : Cl zero
isId O = O ≡ idO

Inp : ∀ j → Cl j → Cl j
Inp zero      𝓓 = isId
Inp (suc j)   𝓓 = 𝓓
Inp (lim f s) 𝓓 = 𝓓

VisT : ∀ i → Cl i
VisT zero      = isId
VisT (suc i)   = Vis (suc (suc i))
VisT (lim f s) = Vis (suc (lim f s))

record Above (j : Ordᴵ) {ℓ} (C′ : Obs ℓ) (D : Obs j) : Set where
  constructor above
  field
    cx′  : Ctx C′
    wrap : ∀ (t : Ordˢ ℓ) → t ≅ˢ t → Σ (Ordˢ j) λ u → (u ≅ˢ u) × (Ωˢ j ⊑ᴱ u) × (run C′ t ≅ˢ run D u)
open Above public

_⟨_⟩ : ∀ {ℓ j} → (Obs ℓ → Obs j) → Cl ℓ → Cl j
_⟨_⟩ W 𝓔 D = Ctx D × (Σ _ λ C → 𝓔 C × (D ≈ᵒ W C))

Dn : ∀ {k ℓ} → k ◃₁ ℓ → Cl ℓ → Cl k
Dn {k = zero}    r 𝓖 = isId
Dn {k = suc _}   r 𝓖 = λ D → Ctx D × (Σ _ λ C → 𝓖 C × (D ≈ᵒ C))
Dn {k = lim _ _} r 𝓖 = λ D → Ctx D × (Σ _ λ C → 𝓖 C × (D ≈ᵒ C))

_∧_ : ∀ {ℓ} → Cl ℓ → Cl ℓ → Cl ℓ
(𝓖 ∧ 𝓑) C = 𝓖 C × 𝓑 C

Wit : ∀ i → Cl i → Set
Wit zero      𝓖 = 𝓖 idO
Wit (suc _)   𝓖 = ⊤
Wit (lim _ _) 𝓖 = ⊤

wit-nz : ∀ i {𝓖 : Cl i} → NZ i → Wit i 𝓖
wit-nz (suc _)   nz = tt
wit-nz (lim _ _) nz = tt

wit-map : ∀ i {𝓖 𝓖′ : Cl i} → (∀ {C} → 𝓖′ C → 𝓖 C) → Wit i 𝓖′ → Wit i 𝓖
wit-map zero      h w = h w
wit-map (suc _)   h w = tt
wit-map (lim _ _) h w = tt

record FlOver {ℓ} (a : Ordˢ ℓ) (O C″ : Obs ℓ) : Set where
  constructor flo-over
  field
    cxo : Ctx C″
    flw : ∀ (t : Ordˢ ℓ) → t ≅ˢ t → (G : Goodᴺ (toZ (run C″ t))) → Σ (Goodᴺ (toZ (run O a))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
open FlOver public
```

## §2 遗传好树

```agda
module _ (ℓ : Ordᴵ) (G< : Bool → (i : Ordᴵ) (r : i ◃ ℓ) → Cl i → Uˢ i r → Set₁) where
  data Good₊ : Bool → Cl ℓ → Ordˢ ℓ → Set₁ where
    bz : ∀ {s 𝓖} → Good₊ s 𝓖 Ord₊ˢ.zero
    b1 : ∀ {𝓖} → ℓ ≅ᴵ zero → Good₊ true 𝓖 (Ord₊ˢ.suc Ord₊ˢ.zero)
    bs : ∀ {s 𝓖} {a : Ordˢ ℓ} (𝓚 : Cl ℓ) → (∀ {C} → 𝓖 C → 𝓚 C) → a ≅ˢ a → Good₊ s 𝓚 a →
         (NZ ℓ → ∀ {O C″} → 𝓚 O → FlOver a O C″ → 𝓚 C″) → (NZ ℓ → ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C) → (∀ {C} → 𝓚 C → Hon ℓ a C) → Good₊ s 𝓖 (Ord₊ˢ.suc a)
    bl : ∀ {s 𝓖} {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ s 𝓖 (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ s 𝓖 (Ord₊ˢ.lim h)
    bi : ∀ {s 𝓖 j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ}
         (𝓖₀ : Cl ℓ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs ℓ → Obs j) →
         (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ p) u))) →
         (∀ (𝓔 : Cl ℓ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z →
            G< true j (<→◃ p) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ p) z) → Good₊ s 𝓔 (f (intoˢ (<→◃ p) z))) →
         (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
         (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
         (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
         Good₊ s 𝓖 (Ord₊ˢ.limᵢ p f)
    bu : ∀ {𝓖 k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< true k (◃₁→◃ r) (Dn r 𝓖) x → Good₊ true 𝓖 (Ord₊ˢ.up r x)
    bŝ : ∀ {s 𝓖 c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} (𝓑 : Ordᴵ → Cl ℓ) →
         (∀ {η η′ C} → η ≅ᴵ η′ → 𝓑 η C → 𝓑 η′ C) →
         Good₊ s 𝓖 t₀ → (∀ η e → Wit ℓ (𝓖 ∧ 𝓑 η) → Good₊ s (𝓖 ∧ 𝓑 η) (g η e)) →
         t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
         (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → c ⊑ᴵ lvG G) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → c ⊑ᴵ lvG G) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → 𝓑 (lvG G) C) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → 𝓑 (lvG G) C) →
         Good₊ s 𝓖 (Ord₊ˢ.ŝ c t₀ g)
    bĉ : ∀ {s 𝓖 c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
         (ys : ℕ → Ordᶜ zero) (hy : ∀ m → HS (ys m)) (dy : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m))
         (G₀ : Goodᴺ t₀) (l₀ : forceᴺ t₀ G₀ ≅ ys 0)
         (Gg : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy m)))
         (lE : ∀ m → forceᴺ _ (Gg m) ≅ ys (suc m)) →
         Good₊ s 𝓖 o₀ → (∀ k → Good₊ s 𝓖 (o (toLevel (ys k) (hy k)) (dy k))) →
         o₀ ⊑ᵒ o (toLevel (ys 0) (hy 0)) (dy 0) → (∀ k → o (toLevel (ys k) (hy k)) (dy k) ⊑ᵒ o (toLevel (ys (suc k)) (hy (suc k))) (dy (suc k))) →
         Good₊ s 𝓖 (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

Gd : ∀ {ℓ} → Bool → (i : Ordᴵ) (r : i ◃ ℓ) → Cl i → Uˢ i r → Set₁
Gd s i zero         𝓖 x = Good₊ i Gd s 𝓖 x
Gd s i (suc r)      𝓖 x = Gd s i r 𝓖 x
Gd s _ (self {f} n) 𝓖 x = Good₊ (f n) Gd s 𝓖 x
Gd s i (lim n r)    𝓖 x = Gd s i r 𝓖 x

Good : ∀ {ℓ} → Bool → Cl ℓ → Ordˢ ℓ → Set₁
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ s 𝓖} (r : i ◃ ℓ) {x : Ordˢ i} → Gd s i r 𝓖 (intoˢ r x) → Good s 𝓖 x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ s 𝓖} (r : i ◃ ℓ) {x : Ordˢ i} → Good s 𝓖 x → Gd s i r 𝓖 (intoˢ r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g
```

## §3 类单调与第 0 层证书

```agda
dn-map : ∀ {k ℓ} (r : k ◃₁ ℓ) {𝓖 𝓖′ : Cl ℓ} → (∀ {C} → 𝓖′ C → 𝓖 C) → ∀ {D} → Dn r 𝓖′ D → Dn r 𝓖 D
dn-map {k = zero}    r h x = x
dn-map {k = suc _}   r h (x , C , c , o) = x , C , h c , o
dn-map {k = lim _ _} r h (x , C , c , o) = x , C , h c , o

Good-mono : ∀ {ℓ s} {𝓖 𝓖′ : Cl ℓ} {x : Ordˢ ℓ} → (∀ {C} → 𝓖′ C → 𝓖 C) → Good s 𝓖 x → Good s 𝓖′ x
Good-mono h bz = bz
Good-mono h (b1 lz) = b1 lz
Good-mono h (bs 𝓚 v ea g clk cgk ho) = bs 𝓚 (λ c → v (h c)) ea g clk cgk ho
Good-mono h (bl hg st) = bl (λ n → Good-mono h (hg n)) st
Good-mono h (bi 𝓖₀ inc W Wf hb Wv St cg hm) = bi 𝓖₀ (λ c → inc (h c)) W Wf hb Wv St cg hm
Good-mono h (bu {r = zero} g)   = bu {r = zero} (Good-mono (dn-map zero h) g)
Good-mono h (bu {r = self n} g) = bu {r = self n} (Good-mono (dn-map (self n) h) g)
Good-mono h (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) =
  bŝ 𝓑 Bc (Good-mono h g0) (λ η e w → Good-mono (λ { (c , b) → h c , b }) (gg η e (wit-map _ (λ { (c , b) → h c , b }) w)))
     et eg m mm (λ c G → d₀ (h c) G) (λ η e c b G → dE η e (h c) b G) (λ c G → ch₀ (h c) G) (λ η e c b G → chS η e (h c) b G)
Good-mono h (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) = bĉ ys hy dy G₀ l₀ Gg lE (Good-mono h go) (λ k → Good-mono h (gO k)) mo mO

record Pt₀ (c : Ordᴵ) (B : Ordᴵ → Set) : Set where
  constructor pt
  field
    Yp : Ordᶜ zero
    hp : HS Yp
    dp : c ⊑ᴵ toLevel Yp hp
    bp : B (toLevel Yp hp)
open Pt₀ public

Good→N : ∀ {s} {𝓖 : Cl zero} {x : Ordˢ zero} → 𝓖 idO → Good s 𝓖 x → Goodᴺ (toZ x)
Good→N i bz = gz
Good→N i (b1 lz) = gs gz
Good→N i (bs 𝓚 v ea g clk cgk ho) = gs (Good→N (v i) g)
Good→N i (bl hg st) = gl (λ n → Good→N i (hg n)) (λ n → st n idO (Good→N i (hg n)) (Good→N i (hg (suc n))))
Good→N i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm)
Good→N i (bu {r = ()} g)
Good→N {𝓖 = 𝓖} i (bŝ {c = c} {t₀ = t₀} {g = g} 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) =
  gc (λ k → Yp (P k)) (λ k → hp (P k)) (λ k → dp (P k)) G₀ (≅-refl⁰ _) Gk (λ k → ≅-refl⁰ _) G₀ Gk
     (m _ (dp (P 0)) idO G₀ (Gk 0))
     (λ k → mm _ (dp (P k)) _ (dp (P (suc k))) (toLevel-⊑ (hp (P k)) (hp (P (suc k))) (Ymono k)) idO (Gk k) (Gk (suc k)))
  where
  G₀ : Goodᴺ (toZ t₀)
  G₀ = Good→N i g0
  P  : ℕ → Pt₀ c (λ η → 𝓑 η idO)
  Gk : ∀ k → Goodᴺ (toZ (g (toLevel (Yp (P k)) (hp (P k))) (dp (P k))))
  P zero    = pt (forceᴺ _ G₀) (forceᴺ-HS _ G₀) (d₀ i G₀) (ch₀ i G₀)
  P (suc k) = pt (forceᴺ _ (Gk k)) (forceᴺ-HS _ (Gk k)) (dE _ (dp (P k)) i (bp (P k)) (Gk k)) (chS _ (dp (P k)) i (bp (P k)) (Gk k))
  Gk k = Good→N (i , bp (P k)) (gg _ (dp (P k)) (i , bp (P k)))
  Ymono : ∀ k → Yp (P k) ⊑⁰ Yp (P (suc k))
  Ymono zero    = m _ (dp (P 0)) idO G₀ (Gk 0)
  Ymono (suc k) = mm _ (dp (P k)) _ (dp (P (suc k))) (toLevel-⊑ (hp (P k)) (hp (P (suc k))) (Ymono k)) idO (Gk k) (Gk (suc k))
Good→N i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) =
  gc ys hy dy G₀ l₀ Gg lE (Good→N i go) (λ k → Good→N i (gO k))
     (mo idO (Good→N i go) (Good→N i (gO 0))) (λ k → mO k idO (Good→N i (gO k)) (Good→N i (gO (suc k))))
```

## §4 语义引理: 观测的关系、读数、上下文的下移

```agda
≈-sym : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O
≈-sym idO = idO
≈-sym (tlo o) = tlo (≈ᶜ-sym o)
≈-sym (addo o k e) = addo (≈-sym o) (≅ᴵ-sym k) (≅ˢ-sym e)
≈-sym (tro o) = tro (≈-sym o)
≈-sym (tr⁻o o) = tr⁻o (≈-sym o)

≈-trans : ∀ {k k′ k″} {O : Obs k} {O′ : Obs k′} {O″ : Obs k″} → O ≈ᵒ O′ → O′ ≈ᵒ O″ → O ≈ᵒ O″
≈-trans idO idO = idO
≈-trans (tlo o) (tlo o′) = tlo (≈ᶜ-trans o o′)
≈-trans (addo o k e) (addo o′ k′ e′) = addo (≈-trans o o′) (≅ᴵ-trans k k′) (≅ˢ-trans e e′)
≈-trans (tro o) (tro o′) = tro (≈-trans o o′)
≈-trans (tr⁻o o) (tr⁻o o′) = tr⁻o (≈-trans o o′)

pull : ∀ {X Y : Ordˢ zero} {c} → X ≅ˢ Y → (∀ (H : Goodᴺ (toZ Y)) → c ⊑ᴵ lvG H) → (G : Goodᴺ (toZ X)) → c ⊑ᴵ lvG G
pull d k G = ⊑ᴵ-≅ʳ (k (Goodᴺ-tr (toZ-≅ d) G)) (toLevel-≅ (forceᴺ-HS _ (Goodᴺ-tr (toZ-≅ d) G)) (forceᴺ-HS _ G) (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) G) G))

τ₁ : ∀ {k ℓ} → k ◃₁ ℓ → Simᴵ k ℓ
τ₁ zero     q = suc q
τ₁ (self n) q = lim n q

sh : ∀ {k ℓ} → k ◃₁ ℓ → Obs ℓ → Obs k
sh {k} {ℓ} r (tlo C) = tlo (wkC (λ v → toFlo k (λ q → cvFlo ℓ v (τ₁ r q))) C)
sh r (addo O a σ) = addo O a (λ q → σ (τ₁ r q))
sh zero (tro O (s≅ e)) = tro (sh zero O) e
sh (self n) (tro O (l≅ f)) = tro (sh (self n) O) (f n)
sh zero (tr⁻o O (s≅ e)) = tr⁻o (sh zero O) e
sh (self n) (tr⁻o O (l≅ f)) = tr⁻o (sh (self n) O) (f n)

sh-≈ : ∀ {k ℓ} (r : k ◃₁ ℓ) (C : Obs ℓ) → Ctx C → sh r C ≈ᵒ C
sh-≈ {k} {ℓ} r (tlo C) c = tlo (≈ᶜ-wkˡ (λ v → toFlo k (λ q → cvFlo ℓ v (τ₁ r q))) (ctxᶜ-refl C c))
sh-≈ r (addo O a σ) (afl e _ _ , c) = addo (ctx-refl O c) (≅ᴵ-refl _) e
sh-≈ zero (tro O (s≅ e)) c = tro (sh-≈ zero O c)
sh-≈ (self n) (tro O (l≅ f)) c = tro (sh-≈ (self n) O c)
sh-≈ zero (tr⁻o O (s≅ e)) c = tr⁻o (sh-≈ zero O c)
sh-≈ (self n) (tr⁻o O (l≅ f)) c = tr⁻o (sh-≈ (self n) O c)

Vis-≈ : ∀ {K k} {C C′ : Obs k} → Ctx C → C ≈ᵒ C′ → Vis K C′ → Vis K C
Vis-≈ c₀ o (vis cx cp) = vis c₀ (λ b t et fl G → pull (run-≅ o et) (cp b t et fl) G)

Vis-lift : ∀ {K k ℓ} (r : k ◃₁ ℓ) {D : Obs k} {C : Obs ℓ} → Ctx D → D ≈ᵒ C → Vis K C → Vis K D
Vis-lift zero {D} c₀ o (vis cx cp) = vis c₀ (λ {b} h t et fl G →
  pull (run-≅ o (upʳ {r = zero} {y = t} et)) (cp h (Ord₊ˢ.up zero t) (upˡ {r = zero} (upʳ {r = zero} et)) (λ ex h₀ → up-rᴱ {r = zero} {y = t} (fl ex h₀))) G)
Vis-lift (self n) {D} c₀ o (vis cx cp) = vis c₀ (λ {b} h t et fl G →
  pull (run-≅ o (upʳ {r = self n} {y = t} et)) (cp h (Ord₊ˢ.up (self n) t) (upˡ {r = self n} (upʳ {r = self n} et)) (λ ex h₀ → up-rᴱ {r = self n} {y = t} (fl ex h₀))) G)
```

## §5 $\Omega_\eta$ 是好的: 类 `Vis η`

```agda
Ωlt : ∀ {b x K} → b ≅ᴵ x → x <ᴵ K → Ωˢ b ⊑ᴱ Ωˢ K
Ωlt e zero      = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (≅→⊑ᴱ (≅ˢ-trans (Ωˢ-≅ e) (≅ˢ-sym d))))
Ωlt e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ωlt e q) (≅ˢ-sym d)))
Ωlt e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (Ωlt e q))

Ctx-sh : ∀ {k ℓ} (r : k ◃₁ ℓ) (C : Obs ℓ) → Ctx C → Ctx (sh r C)
Ctx-sh r (tlo C) c = Ctx-wkC C c
Ctx-sh r (addo O a σ) c = c
Ctx-sh zero (tro O (s≅ e)) c = Ctx-sh zero O c
Ctx-sh (self n) (tro O (l≅ f)) c = Ctx-sh (self n) O c
Ctx-sh zero (tr⁻o O (s≅ e)) c = Ctx-sh zero O c
Ctx-sh (self n) (tr⁻o O (l≅ f)) c = Ctx-sh (self n) O c

Vis-mono : ∀ {K K′ k} {C : Obs k} → (∀ {b} → b ≺ᴵ K′ → b ≺ᴵ K) → Vis K C → Vis K′ C
Vis-mono h (vis cx cp) = vis cx (λ b → cp (h b))

fl-tr⁻ : ∀ {k₀ a b} (e : a ≅ᴵ b) {x : Ordˢ k₀} {t : Ordˢ b} → x ≅ˢ x → x ⊑ᴱ t → x ⊑ᴱ tr⁻ˢ e t
fl-tr⁻ {k₀} e {x} ex h {O} {O′} o G′ =
  Goodᴺ-tr (toZ-≅ d) (proj₁ L) , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) (proj₁ L)) (proj₁ L))) (proj₂ L)
  where
  L = h {O = tr⁻o O (≅ᴵ-refl k₀)} {O′ = tr⁻o O′ e} (tr⁻o o) G′
  d : run (tr⁻o O (≅ᴵ-refl k₀)) x ≅ˢ run O x
  d = run-≅ (≈ᵒ-reflˡ o) (tr⁻ˢ-≅ (≅ᴵ-refl k₀) ex)

fl-tr : ∀ {k₀ a b} (e : a ≅ᴵ b) {x : Ordˢ k₀} {t : Ordˢ a} → x ≅ˢ x → x ⊑ᴱ t → x ⊑ᴱ trˢ e t
fl-tr {k₀} e {x} ex h {O} {O′} o G′ =
  Goodᴺ-tr (toZ-≅ d) (proj₁ L) , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) (proj₁ L)) (proj₁ L))) (proj₂ L)
  where
  L = h {O = tro O (≅ᴵ-refl k₀)} {O′ = tro O′ e} (tro o) G′
  d : run (tro O (≅ᴵ-refl k₀)) x ≅ˢ run O x
  d = run-≅ (≈ᵒ-reflˡ o) (trˢ-≅ (≅ᴵ-refl k₀) ex)

⊑ᴱ-Ω≅ : ∀ {k₀ a b} {x : Ordˢ k₀} → x ≅ˢ x → a ≅ᴵ b → x ⊑ᴱ Ωˢ a → x ⊑ᴱ Ωˢ b
⊑ᴱ-Ω≅ ex e h = ⊑ᴱ-≅ʳ (fl-tr e ex h) (trˢ-≅ e (Ωˢ-≅ e))

ΩTr : ∀ {k₀ b x K} {y : Ordˢ k₀} → y ≅ˢ y → y ⊑ᴱ Ωˢ b → b ≅ᴵ x → x <ᴵ K → y ⊑ᴱ Ωˢ K
ΩTr ey h e zero      = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (⊑ᴱ-Ω≅ ey e h) (≅ˢ-sym d)))
ΩTr ey h e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (ΩTr ey h e q) (≅ˢ-sym d)))
ΩTr ey h e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (ΩTr ey h e q))

Ωup : ∀ {k₀ b c} {y : Ordˢ k₀} → y ≅ˢ y → y ⊑ᴱ Ωˢ b → b ≺ᴵ suc c → y ⊑ᴱ Ωˢ c
Ωup ey h (via e zero)    = ⊑ᴱ-Ω≅ ey e h
Ωup ey h (via e (suc q)) = ΩTr ey h e q

St-Ω : ∀ {c ℓ₀} {C : Obs (suc c)} {C′ : Obs ℓ₀} → Vis (suc c) C → Above c C′ (sh zero C) → Vis (suc c) C′
St-Ω {c} {C = C} v (above cx′ wrap) = vis cx′ (λ {b} h t et _ G →
  let u = proj₁ (wrap t et)
      eu = proj₁ (proj₂ (wrap t et))
      fu = proj₁ (proj₂ (proj₂ (wrap t et)))
      d  = proj₂ (proj₂ (proj₂ (wrap t et)))
  in pull (≅ˢ-trans d (run-≅ (sh-≈ zero C (cx v)) (upʳ {r = zero} {y = u} eu)))
          (cp v h (Ord₊ˢ.up zero u) (upˡ {r = zero} (upʳ {r = zero} eu)) (λ ex h₀ → up-rᴱ {r = zero} {y = u} (⊑ᴱ-trans (Ωup ex h₀ h) fu))) G)

dn→inp : ∀ c {𝓔 : Cl (suc c)} → (∀ {C} → 𝓔 C → Vis (suc c) C) → ∀ {D} → Dn zero 𝓔 D → Inp c (sh zero ⟨ 𝓔 ⟩) D
dn→inp zero h x = x
dn→inp (suc c) h {D} (x , C , cc , o) = x , C , cc , ≈-trans o (≈-sym (sh-≈ zero C (cx (h cc))))
dn→inp (lim f s) h {D} (x , C , cc , o) = x , C , cc , ≈-trans o (≈-sym (sh-≈ zero C (cx (h cc))))

dn→vis : ∀ {k ℓ} (r : k ◃₁ ℓ) {D} → Dn r (Vis ℓ) D → Vis k D
dn→vis {k = zero} r {D} refl = vis tt (λ { (via e ()) })
dn→vis {k = suc _} r (x , C , cc , o) = Vis-mono (λ { (via e q) → via e (τ₁ r q) }) (Vis-lift r x o cc)
dn→vis {k = lim _ _} r (x , C , cc , o) = Vis-mono (λ { (via e q) → via e (τ₁ r q) }) (Vis-lift r x o cc)

Ωg : ∀ η → Good true (Vis η) (Ωˢ η)
Ωg zero      = b1 z≅
Ωg (suc c)   = bi (Vis (suc c)) (λ v → v) (sh zero)
  (λ {C} v u eu → run-≅ (sh-≈ zero C (cx v)) (upʳ {r = zero} {y = u} eu))
  (λ 𝓔 inc z ez g → bu {r = zero} (Good-mono (dn→inp c inc) g))
  (λ {C} v → Vis-lift zero (Ctx-sh zero C (cx v)) (sh-≈ zero C (cx v)) v)
  St-Ω
  (λ c₀ o v → Vis-≈ c₀ o v)
  (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
Ωg (lim g s) = bl (λ n → bu {r = self n} (Good-mono (dn→vis (self n)) (Ωg (g n))))
                  (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))
```

## §6 第 0 层的搬运

```agda
lvl≅ : ∀ {X Y : Ordˢ zero} (d : X ≅ˢ Y) (G : Goodᴺ (toZ X)) → lvG (Goodᴺ-tr (toZ-≅ d) G) ≅ᴵ lvG G
lvl≅ d G = toLevel-≅ (forceᴺ-HS _ (Goodᴺ-tr (toZ-≅ d) G)) (forceᴺ-HS _ G) (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) G) G)

Tr₀ : ∀ {s} {𝓧 : Cl zero} {x : Ordˢ zero} → 𝓧 idO → Good s 𝓧 x → x ≅ˢ x → Good s isId (trˢ z≅ x)
Tr₀ i bz ex = bz
Tr₀ i (b1 lz) ex = b1 lz
Tr₀ i (bs 𝓚 v ea g clk cgk ho) ex = bs isId (λ c → c) (self-trˢ z≅ ea) (Tr₀ (v i) g ea) (λ ()) (λ ()) (λ _ _ → z⊑)
Tr₀ i (bl hg st) ex = bl (λ n → Tr₀ i (hg n) (l-invˢ ex n)) (λ n → tr-cong (st n))
Tr₀ i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm) ex
Tr₀ i (bu {r = ()} g) ex
Tr₀ i (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η _ → 𝓑 η idO) (λ e b → Bc e b) (Tr₀ i g0 et)
     (λ η e w → Good-mono proj₁ (Tr₀ (i , proj₂ w) (gg η e (i , proj₂ w)) (eg η e η e (≅ᴵ-refl η))))
     (self-trˢ z≅ et) (λ η e η′ e′ eη → trˢ-≅ z≅ (≅-trˢ z≅ (eg η e η′ e′ eη)))
     (λ η e → tr-cong (m η e)) (λ η e η′ e′ h → tr-cong (mm η e η′ e′ h))
     (λ { refl G → pull (trˢ-≅ z≅ et) (d₀ i) G })
     (λ { η e refl b G → pull (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) (dE η e i b) G })
     (λ { refl G → Bc (lvl≅ (trˢ-≅ z≅ et) G) (ch₀ i (Goodᴺ-tr (toZ-≅ (trˢ-≅ z≅ et)) G)) })
     (λ { η e refl b G → Bc (lvl≅ (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) G) (chS η e i b (Goodᴺ-tr (toZ-≅ (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η)))) G)) })
Tr₀ i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr₀ i go (ĉ-refl₀ ex)) (λ k → Tr₀ i (gO k) (ĉ-reflg ex _ _)) (tr-cong mo) (λ k → tr-cong (mO k))

Tr⁻₀ : ∀ {s} {𝓧 : Cl zero} {x : Ordˢ zero} → 𝓧 idO → Good s 𝓧 x → x ≅ˢ x → Good s isId (tr⁻ˢ z≅ x)
Tr⁻₀ i bz ex = bz
Tr⁻₀ i (b1 lz) ex = b1 lz
Tr⁻₀ i (bs 𝓚 v ea g clk cgk ho) ex = bs isId (λ c → c) (self-tr⁻ˢ z≅ ea) (Tr⁻₀ (v i) g ea) (λ ()) (λ ()) (λ _ _ → z⊑)
Tr⁻₀ i (bl hg st) ex = bl (λ n → Tr⁻₀ i (hg n) (l-invˢ ex n)) (λ n → tr⁻-cong (st n))
Tr⁻₀ i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm) ex
Tr⁻₀ i (bu {r = ()} g) ex
Tr⁻₀ i (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η _ → 𝓑 η idO) (λ e b → Bc e b) (Tr⁻₀ i g0 et)
     (λ η e w → Good-mono proj₁ (Tr⁻₀ (i , proj₂ w) (gg η e (i , proj₂ w)) (eg η e η e (≅ᴵ-refl η))))
     (self-tr⁻ˢ z≅ et) (λ η e η′ e′ eη → tr⁻ˢ-≅ z≅ (≅-tr⁻ˢ z≅ (eg η e η′ e′ eη)))
     (λ η e → tr⁻-cong (m η e)) (λ η e η′ e′ h → tr⁻-cong (mm η e η′ e′ h))
     (λ { refl G → pull (tr⁻ˢ-≅ z≅ et) (d₀ i) G })
     (λ { η e refl b G → pull (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) (dE η e i b) G })
     (λ { refl G → Bc (lvl≅ (tr⁻ˢ-≅ z≅ et) G) (ch₀ i (Goodᴺ-tr (toZ-≅ (tr⁻ˢ-≅ z≅ et)) G)) })
     (λ { η e refl b G → Bc (lvl≅ (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) G) (chS η e i b (Goodᴺ-tr (toZ-≅ (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η)))) G)) })
Tr⁻₀ i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr⁻₀ i go (ĉ-refl₀ ex)) (λ k → Tr⁻₀ i (gO k) (ĉ-reflg ex _ _)) (tr⁻-cong mo) (λ k → tr⁻-cong (mO k))
```

## §7 非零层的搬运

```agda
NZ-e : ∀ {a b} → a ≅ᴵ b → NZ b → NZ a
NZ-e (s≅ _) nz = tt
NZ-e (l≅ _) nz = tt
NZ-e z≅ ()

NZ-e′ : ∀ {a b} → a ≅ᴵ b → NZ a → NZ b
NZ-e′ (s≅ _) nz = tt
NZ-e′ (l≅ _) nz = tt
NZ-e′ z≅ ()

bkO : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) → Obs j → Obs (repˢ (resˢ q e))
bkO zero      (s≅ e) D = tr⁻o D e
bkO (suc q)   (s≅ e) D = bkO q e D
bkO (lim n q) (l≅ f) D = bkO q (f n) D

rb : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Obs j) (u : Ordˢ (repˢ (resˢ q e))) → run (bkO q e D) u ≡ run D (backˢ (resˢ q e) u)
rb zero      (s≅ e) D u = refl
rb (suc q)   (s≅ e) D u = rb q e D u
rb (lim n q) (l≅ f) D u = rb q (f n) D u

cb : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Obs j) → Ctx D → Ctx (bkO q e D)
cb zero      (s≅ e) D c = c
cb (suc q)   (s≅ e) D c = cb q e D c
cb (lim n q) (l≅ f) D c = cb q (f n) D c

ob : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {D D′ : Obs j} → D ≈ᵒ D′ → bkO q e D ≈ᵒ bkO q e D′
ob zero      (s≅ e) o = tr⁻o o
ob (suc q)   (s≅ e) o = ob q e o
ob (lim n q) (l≅ f) o = ob q (f n) o

fb : ∀ {k₀ j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {x : Ordˢ k₀} {u : Ordˢ (repˢ (resˢ q e))} → x ≅ˢ x → x ⊑ᴱ u → x ⊑ᴱ backˢ (resˢ q e) u
fb zero      (s≅ e) ex h = fl-tr⁻ e ex h
fb (suc q)   (s≅ e) ex h = fb q e ex h
fb (lim n q) (l≅ f) ex h = fb q (f n) ex h

bm : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (resˢ q e))} → u ⊑ᵒ u′ → backˢ (resˢ q e) u ⊑ᵒ backˢ (resˢ q e) u′
bm zero      (s≅ e) h = tr⁻-cong h
bm (suc q)   (s≅ e) h = bm q e h
bm (lim n q) (l≅ f) h = bm q (f n) h

bkO⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) → Obs j → Obs (repˢ (res⁻ˢ q e))
bkO⁻ zero      (s≅ e) D = tro D e
bkO⁻ (suc q)   (s≅ e) D = bkO⁻ q e D
bkO⁻ (lim n q) (l≅ f) D = bkO⁻ q (f n) D

rb⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (D : Obs j) (u : Ordˢ (repˢ (res⁻ˢ q e))) → run (bkO⁻ q e D) u ≡ run D (backˢ (res⁻ˢ q e) u)
rb⁻ zero      (s≅ e) D u = refl
rb⁻ (suc q)   (s≅ e) D u = rb⁻ q e D u
rb⁻ (lim n q) (l≅ f) D u = rb⁻ q (f n) D u

cb⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (D : Obs j) → Ctx D → Ctx (bkO⁻ q e D)
cb⁻ zero      (s≅ e) D c = c
cb⁻ (suc q)   (s≅ e) D c = cb⁻ q e D c
cb⁻ (lim n q) (l≅ f) D c = cb⁻ q (f n) D c

ob⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {D D′ : Obs j} → D ≈ᵒ D′ → bkO⁻ q e D ≈ᵒ bkO⁻ q e D′
ob⁻ zero      (s≅ e) o = tro o
ob⁻ (suc q)   (s≅ e) o = ob⁻ q e o
ob⁻ (lim n q) (l≅ f) o = ob⁻ q (f n) o

fb⁻ : ∀ {k₀ j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {x : Ordˢ k₀} {u : Ordˢ (repˢ (res⁻ˢ q e))} → x ≅ˢ x → x ⊑ᴱ u → x ⊑ᴱ backˢ (res⁻ˢ q e) u
fb⁻ zero      (s≅ e) ex h = fl-tr e ex h
fb⁻ (suc q)   (s≅ e) ex h = fb⁻ q e ex h
fb⁻ (lim n q) (l≅ f) ex h = fb⁻ q (f n) ex h

bm⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (res⁻ˢ q e))} → u ⊑ᵒ u′ → backˢ (res⁻ˢ q e) u ⊑ᵒ backˢ (res⁻ˢ q e) u′
bm⁻ zero      (s≅ e) h = tr-cong h
bm⁻ (suc q)   (s≅ e) h = bm⁻ q e h
bm⁻ (lim n q) (l≅ f) h = bm⁻ q (f n) h

sbk : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → backˢ (resˢ q e) u ≅ˢ backˢ (resˢ q e) u
sbk q e d = ≅ˢ-reflˡ (backˢ-≅ q e d)

sbk⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → backˢ (res⁻ˢ q e) u ≅ˢ backˢ (res⁻ˢ q e) u
sbk⁻ q e d = ≅ˢ-reflˡ (back⁻ˢ-≅ q e d)

≺s-eq : ∀ {b′ j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) → b′ ≺ᴵ suc (repˢ (resˢ q e)) → b′ ≺ᴵ suc j
≺s-eq q e r = ≺ᴵ-respʳ r (s≅ (≅ᴵ-sym (eqˢ (resˢ q e))))

≺s-eq⁻ : ∀ {b′ j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) → b′ ≺ᴵ suc (repˢ (res⁻ˢ q e)) → b′ ≺ᴵ suc j
≺s-eq⁻ q e r = ≺ᴵ-respʳ r (s≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e))))

Tr  : ∀ {s a b} (e : a ≅ᴵ b) → NZ a → {𝓧 : Cl a} {𝓨 : Cl b} {x : Ordˢ a} → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (tro D e)) → Good s 𝓧 x → x ≅ˢ x → Good s 𝓨 (trˢ e x)
Tr⁻ : ∀ {s a b} (e : a ≅ᴵ b) → NZ b → {𝓧 : Cl b} {𝓨 : Cl a} {x : Ordˢ b} → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (tr⁻o D e)) → Good s 𝓧 x → x ≅ˢ x → Good s 𝓨 (tr⁻ˢ e x)
Bk  : ∀ {s j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (𝓕 : Cl j) (𝓕′ : Cl (repˢ (resˢ q e))) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (bkO q e D)) → ∀ {u} → u ≅ˢ u →
      Good s (Inp _ 𝓕′) u → Good s (Inp j 𝓕) (backˢ (resˢ q e) u)
Bk⁻ : ∀ {s j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (𝓕 : Cl j) (𝓕′ : Cl (repˢ (res⁻ˢ q e))) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (bkO⁻ q e D)) → ∀ {u} → u ≅ˢ u →
      Good s (Inp _ 𝓕′) u → Good s (Inp j 𝓕) (backˢ (res⁻ˢ q e) u)
Dtr : ∀ {s k k′ ℓ ℓ′} (r : k ◃₁ ℓ) (r′ : k′ ◃₁ ℓ′) (e : k ≅ᴵ k′) {𝓧 : Cl ℓ} {𝓨 : Cl ℓ′} (E : Obs ℓ′ → Obs ℓ) →
      (∀ {D : Obs k′} {D′ : Obs ℓ′} → D ≈ᵒ D′ → tro D e ≈ᵒ E D′) → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (E D)) →
      ∀ {x : Ordˢ k} → Good s (Dn r 𝓧) x → x ≅ˢ x → Good s (Dn r′ 𝓨) (trˢ e x)
Dtr⁻ : ∀ {s k k′ ℓ ℓ′} (r : k′ ◃₁ ℓ′) (r′ : k ◃₁ ℓ) (e : k ≅ᴵ k′) {𝓧 : Cl ℓ′} {𝓨 : Cl ℓ} (E : Obs ℓ → Obs ℓ′) →
      (∀ {D : Obs k} {D′ : Obs ℓ} → D ≈ᵒ D′ → tr⁻o D e ≈ᵒ E D′) → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (E D)) →
      ∀ {x : Ordˢ k′} → Good s (Dn r 𝓧) x → x ≅ˢ x → Good s (Dn r′ 𝓨) (tr⁻ˢ e x)
Bb : ∀ {s j j′} (e : j ≅ᴵ j′) (𝓕 : Cl j) (𝓕′ : Cl j′) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (tr⁻o D e)) → ∀ {u} → u ≅ˢ u → Good s (Inp j′ 𝓕′) u → Good s (Inp j 𝓕) (tr⁻ˢ e u)
Bb⁻ : ∀ {s j j′} (e : j′ ≅ᴵ j) (𝓕 : Cl j) (𝓕′ : Cl j′) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (tro D e)) → ∀ {u} → u ≅ˢ u → Good s (Inp j′ 𝓕′) u → Good s (Inp j 𝓕) (trˢ e u)

Dtr r r′ z≅ E oE M g ex = Tr₀ refl g ex
Dtr r r′ e@(s≅ _) E oE M g ex = Tr e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr r r′ e@(l≅ _) E oE M g ex = Tr e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr⁻ r r′ z≅ E oE M g ex = Tr⁻₀ refl g ex
Dtr⁻ r r′ e@(s≅ _) E oE M g ex = Tr⁻ e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr⁻ r r′ e@(l≅ _) E oE M g ex = Tr⁻ e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex

Bb z≅ 𝓕 𝓕′ M eu g = Tr⁻₀ refl g eu
Bb e@(s≅ _) 𝓕 𝓕′ M eu g = Tr⁻ e tt M g eu
Bb e@(l≅ _) 𝓕 𝓕′ M eu g = Tr⁻ e tt M g eu
Bb⁻ z≅ 𝓕 𝓕′ M eu g = Tr₀ refl g eu
Bb⁻ e@(s≅ _) 𝓕 𝓕′ M eu g = Tr e tt M g eu
Bb⁻ e@(l≅ _) 𝓕 𝓕′ M eu g = Tr e tt M g eu

Bk zero      (s≅ e) 𝓕 𝓕′ M eu g = Bb e 𝓕 𝓕′ M eu g
Bk (suc q)   (s≅ e) 𝓕 𝓕′ M eu g = Bk q e 𝓕 𝓕′ M eu g
Bk (lim n q) (l≅ f) 𝓕 𝓕′ M eu g = Bk q (f n) 𝓕 𝓕′ M eu g
Bk⁻ zero      (s≅ e) 𝓕 𝓕′ M eu g = Bb⁻ e 𝓕 𝓕′ M eu g
Bk⁻ (suc q)   (s≅ e) 𝓕 𝓕′ M eu g = Bk⁻ q e 𝓕 𝓕′ M eu g
Bk⁻ (lim n q) (l≅ f) 𝓕 𝓕′ M eu g = Bk⁻ q (f n) 𝓕 𝓕′ M eu g

Tr e nz M bz ex = bz
Tr e nz M (b1 lz) ex = b1 (≅ᴵ-trans (≅ᴵ-sym e) lz)
Tr e nz M (bs 𝓚 v ea g clk cgk ho) ex =
  bs (λ D → Ctx D × 𝓚 (tro D e)) (λ c → proj₁ (M c) , v (proj₂ (M c))) (self-trˢ e ea) (Tr e nz (λ c → c) g ea)
     (λ nz₂ (x , c) fo′ → cxo fo′ , clk (NZ-e e nz₂) c (flo-over (cxo fo′) (λ t et G → flw fo′ (trˢ e t) (self-trˢ e et) G)))
     (λ nz₂ c₀ o (x , c) → c₀ , cgk (NZ-e e nz₂) c₀ (tro o) c) (λ (x , c) G → ⊑ᴵ-≅ˡ e (ho c G))
Tr e nz M (bl hg st) ex = bl (λ n → Tr e nz M (hg n) (l-invˢ ex n)) (λ n → tr-cong (st n))
Tr {s = s} e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bi {j = j} {p = q} {f = f} 𝓖₀ inc W Wf hb Wv St cg hm) ex = bi
  (λ D → Ctx D × 𝓖₀ (tro D e))
  (λ c → proj₁ (M c) , inc (proj₂ (M c)))
  (λ D → bkO q e (W (tro D e)))
  (λ {D} (x , c) u eu → subst (λ w → run (bkO q e (W (tro D e))) u ≅ˢ run D (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
       (subst (λ y → y ≅ˢ run D (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))))) (sym (rb q e (W (tro D e)) u)) (Wf c (backˢ (resˢ q e) u) (sbk q e eu))))
  (λ 𝓔′ inc″ z ez g → subst (λ y → Good s 𝓔′ (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) y))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (Tr e nz {𝓧 = λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)} (λ {D} c → proj₁ (inc″ c) , D , c , refl)
          (hb (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)) (λ { (D , c , refl) → proj₂ (inc″ c) })
              (backˢ (resˢ q e) z) (sbk q e ez)
              (Good→Gd (<→◃ q) (Bk q e (W ⟨ (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)) ⟩) ((λ D → bkO q e (W (tro D e))) ⟨ 𝓔′ ⟩)
                  (λ { (x , D₁ , (D , c , refl) , o) → x , cb q e _ x , D , c , ob q e o }) ez (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))
          (i-respˢ ex (sbk q e ez))))
  (λ {D} (x , c) → vis (cb q e _ (cx (Wv c)))
       (λ {b} h t et fl G →
       pull (subst (λ y → y ≅ˢ run (W (tro D e)) (backˢ (resˢ q e) t)) (sym (rb q e (W (tro D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk q e et)))
            (cp (Wv c) (≺s-eq q e h) (backˢ (resˢ q e) t) (sbk q e et) (λ ex₀ h₀ → fb q e ex₀ (fl ex₀ h₀))) G))
  (λ {D} {C″} (x , c) (above cx′ wrap) → cx′ , St c (above cx′ (λ t et →
       let t′ = trˢ e t
           et′ = self-trˢ e et
           u = proj₁ (wrap t′ et′)
           eu = proj₁ (proj₂ (wrap t′ et′))
           fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
           d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
       in backˢ (resˢ q e) u , sbk q e eu , fb q e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ (eqˢ (resˢ q e)))) fu) ,
          subst (λ y → run C″ t′ ≅ˢ y) (rb q e (W (tro D e)) u) d)))
  (λ c₀ o (x , c) → c₀ , cg c₀ (tro o) c)
  (λ {z} {z′} h → subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
       (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′)) (tr-cong (hm (bm q e h))))
Tr (s≅ e′) nz M (bu {r = zero} g) ex = bu {r = zero} (Dtr zero zero e′ (λ D → tro D (s≅ e′)) (λ o → tro o) M g (u-reflˢ zero ex))
Tr (l≅ f) nz M (bu {r = self n} g) ex = bu {r = self n} (Dtr (self n) (self n) (f n) (λ D → tro D (l≅ f)) (λ o → tro o) M g (u-reflˢ (self n) ex))
Tr e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η D → 𝓑 η (tro D e)) Bc (Tr e nz M g0 et)
     (λ η d w → Tr e nz {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c , b) → proj₁ (M c) , proj₂ (M c) , b)
        (gg η d (wit-nz _ nz)) (eg η d η d (≅ᴵ-refl η)))
     (self-trˢ e et) (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
     (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
     (λ c G → d₀ (proj₂ (M c)) G) (λ η d c b G → dE η d (proj₂ (M c)) b G)
     (λ c G → ch₀ (proj₂ (M c)) G) (λ η d c b G → chS η d (proj₂ (M c)) b G)
Tr e nz M (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr e nz M go (ĉ-refl₀ ex)) (λ k → Tr e nz M (gO k) (ĉ-reflg ex _ _)) (tr-cong mo) (λ k → tr-cong (mO k))

Tr⁻ e nz M bz ex = bz
Tr⁻ e nz M (b1 lz) ex = b1 (≅ᴵ-trans e lz)
Tr⁻ e nz M (bs 𝓚 v ea g clk cgk ho) ex =
  bs (λ D → Ctx D × 𝓚 (tr⁻o D e)) (λ c → proj₁ (M c) , v (proj₂ (M c))) (self-tr⁻ˢ e ea) (Tr⁻ e nz (λ c → c) g ea)
     (λ nz₂ (x , c) fo′ → cxo fo′ , clk (NZ-e′ e nz₂) c (flo-over (cxo fo′) (λ t et G → flw fo′ (tr⁻ˢ e t) (self-tr⁻ˢ e et) G)))
     (λ nz₂ c₀ o (x , c) → c₀ , cgk (NZ-e′ e nz₂) c₀ (tr⁻o o) c) (λ (x , c) G → ⊑ᴵ-≅ˡ (≅ᴵ-sym e) (ho c G))
Tr⁻ e nz M (bl hg st) ex = bl (λ n → Tr⁻ e nz M (hg n) (l-invˢ ex n)) (λ n → tr⁻-cong (st n))
Tr⁻ {s = s} e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bi {j = j} {p = q} {f = f} 𝓖₀ inc W Wf hb Wv St cg hm) ex = bi
  (λ D → Ctx D × 𝓖₀ (tr⁻o D e))
  (λ c → proj₁ (M c) , inc (proj₂ (M c)))
  (λ D → bkO⁻ q e (W (tr⁻o D e)))
  (λ {D} (x , c) u eu → subst (λ w → run (bkO⁻ q e (W (tr⁻o D e))) u ≅ˢ run D (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
       (subst (λ y → y ≅ˢ run D (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))))) (sym (rb⁻ q e (W (tr⁻o D e)) u)) (Wf c (backˢ (res⁻ˢ q e) u) (sbk⁻ q e eu))))
  (λ 𝓔′ inc″ z ez g → subst (λ y → Good s 𝓔′ (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) y))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (Tr⁻ e nz {𝓧 = λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)} (λ {D} c → proj₁ (inc″ c) , D , c , refl)
          (hb (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)) (λ { (D , c , refl) → proj₂ (inc″ c) })
              (backˢ (res⁻ˢ q e) z) (sbk⁻ q e ez)
              (Good→Gd (<→◃ q) (Bk⁻ q e (W ⟨ (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)) ⟩) ((λ D → bkO⁻ q e (W (tr⁻o D e))) ⟨ 𝓔′ ⟩)
                  (λ { (x , D₁ , (D , c , refl) , o) → x , cb⁻ q e _ x , D , c , ob⁻ q e o }) ez (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))
          (i-respˢ ex (sbk⁻ q e ez))))
  (λ {D} (x , c) → vis (cb⁻ q e _ (cx (Wv c)))
       (λ {b} h t et fl G →
       pull (subst (λ y → y ≅ˢ run (W (tr⁻o D e)) (backˢ (res⁻ˢ q e) t)) (sym (rb⁻ q e (W (tr⁻o D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk⁻ q e et)))
            (cp (Wv c) (≺s-eq⁻ q e h) (backˢ (res⁻ˢ q e) t) (sbk⁻ q e et) (λ ex₀ h₀ → fb⁻ q e ex₀ (fl ex₀ h₀))) G))
  (λ {D} {C″} (x , c) (above cx′ wrap) → cx′ , St c (above cx′ (λ t et →
       let t′ = tr⁻ˢ e t
           et′ = self-tr⁻ˢ e et
           u = proj₁ (wrap t′ et′)
           eu = proj₁ (proj₂ (wrap t′ et′))
           fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
           d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
       in backˢ (res⁻ˢ q e) u , sbk⁻ q e eu , fb⁻ q e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ (eqˢ (res⁻ˢ q e)))) fu) ,
          subst (λ y → run C″ t′ ≅ˢ y) (rb⁻ q e (W (tr⁻o D e)) u) d)))
  (λ c₀ o (x , c) → c₀ , cg c₀ (tr⁻o o) c)
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
       (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)) (tr⁻-cong (hm (bm⁻ q e h))))
Tr⁻ (s≅ e′) nz M (bu {r = zero} g) ex = bu {r = zero} (Dtr⁻ zero zero e′ (λ D → tr⁻o D (s≅ e′)) (λ o → tr⁻o o) M g (u-reflˢ zero ex))
Tr⁻ (l≅ f) nz M (bu {r = self n} g) ex = bu {r = self n} (Dtr⁻ (self n) (self n) (f n) (λ D → tr⁻o D (l≅ f)) (λ o → tr⁻o o) M g (u-reflˢ (self n) ex))
Tr⁻ e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η D → 𝓑 η (tr⁻o D e)) Bc (Tr⁻ e nz M g0 et)
     (λ η d w → Tr⁻ e nz {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c , b) → proj₁ (M c) , proj₂ (M c) , b)
        (gg η d (wit-nz _ nz)) (eg η d η d (≅ᴵ-refl η)))
     (self-tr⁻ˢ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
     (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
     (λ c G → d₀ (proj₂ (M c)) G) (λ η d c b G → dE η d (proj₂ (M c)) b G)
     (λ c G → ch₀ (proj₂ (M c)) G) (λ η d c b G → chS η d (proj₂ (M c)) b G)
Tr⁻ e nz M (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr⁻ e nz M go (ĉ-refl₀ ex)) (λ k → Tr⁻ e nz M (gO k) (ĉ-reflg ex _ _)) (tr⁻-cong mo) (λ k → tr⁻-cong (mO k))
```

```agda
≈-id : ∀ {C : Obs zero} → C ≈ᵒ idO → C ≡ idO
≈-id idO = refl
```
