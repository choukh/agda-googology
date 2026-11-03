# 无记号主线 (五): `Ordˢ` 上的互模拟

> **`_≅ˢ_`, `toZ-≅`, 与 `Run` 上的 `_≈ᴿ_`, 不用记号.**
> 脚本从 [UniformNF3Eq](../Align/UniformNF3Eq.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Eq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix
open import OCF.Free.Floor
open import OCF.Free.Aux
open import OCF.Free.Prefix public using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; ≅ᶻ-sym; ≅ᶻ-trans; 𝟎ˢ)
open import OCF.Free.Aux public using (kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; tf)
```

```agda
open Ord-Ord using (iter)
open Restrˢ
```

## §1 互模拟

```agda
module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set) where
  data Eq₊ˢ : ∀ {ℓ′} → Ordˢ ℓ → Ordˢ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ˢ {ℓ′} Ord₊ˢ.zero Ord₊ˢ.zero
    s≅  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordˢ ℓ′} → ℓ ≅ᴵ ℓ′ → Eq₊ˢ a b → Eq₊ˢ (Ord₊ˢ.suc a) (Ord₊ˢ.suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eq₊ˢ (f n) (g n)) → Eq₊ˢ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lᵢ≅ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : Uˢ j′ (<→◃ q) → Ordˢ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordˢ j′) → R j (<→◃ p) (intoˢ (<→◃ p) x) y → Eq₊ˢ (f (intoˢ (<→◃ p) x)) (g (intoˢ (<→◃ q) y))) →
          Eq₊ˢ (Ord₊ˢ.limᵢ p f) (Ord₊ˢ.limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {b : Ordˢ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ˢ (Ord₊ˢ.up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : Uˢ k (◃₁→◃ r)} {a : Ordˢ ℓ} → Eq₊ˢ a (outˢ (◃₁→◃ r) y) → Eq₊ˢ a (Ord₊ˢ.up r y)
    ŝ≅  : ∀ {ℓ′ c c′} {t₀ : Ordˢ ℓ} {t₀′ : Ordˢ ℓ′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          kd ℓ ≡ kd ℓ′ → c ≅ᴵ c′ → Eq₊ˢ t₀ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eq₊ˢ (g η e) (g′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ŝ c t₀ g) (Ord₊ˢ.ŝ c′ t₀′ g′)
    ĉ≅  : ∀ {ℓ′ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
          {o₀ : Ordˢ ℓ} {o₀′ : Ordˢ ℓ′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
          Eq₊ˢ o₀ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eq₊ˢ (o η e) (o′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (Ord₊ˢ.ĉᴸ c′ t₀′ g′ o₀′ o′)

Rˢ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set
Rˢ i zero         x b = Eq₊ˢ i Rˢ x b
Rˢ i (suc r)      x b = Rˢ i r x b
Rˢ _ (self {f} n) x b = Eq₊ˢ (f n) Rˢ x b
Rˢ i (lim n r)    x b = Rˢ i r x b

infix 4 _≅ˢ_
_≅ˢ_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordˢ ℓ₂ → Set
_≅ˢ_ {ℓ₁} = Eq₊ˢ ℓ₁ Rˢ

R→≅ˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → Rˢ i r (intoˢ r x) b → x ≅ˢ b
R→≅ˢ zero      e = e
R→≅ˢ (suc r)   e = R→≅ˢ r e
R→≅ˢ (self n)  e = e
R→≅ˢ (lim n r) e = R→≅ˢ r e

≅→Rˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → x ≅ˢ b → Rˢ i r (intoˢ r x) b
≅→Rˢ zero      e = e
≅→Rˢ (suc r)   e = ≅→Rˢ r e
≅→Rˢ (self n)  e = e
≅→Rˢ (lim n r) e = ≅→Rˢ r e

R-convˢ : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordˢ j} {b : Ordˢ ℓ′} → Rˢ j r (intoˢ r x) b → Rˢ j r′ (intoˢ r′ x) b
R-convˢ r r′ e = ≅→Rˢ r′ (R→≅ˢ r e)

≅ˢ-sym  : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → b ≅ˢ a
R-flipˢ : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → Rˢ j r (intoˢ r x) y → Rˢ j′ r′ (intoˢ r′ y) x
flipRˢ  : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → x ≅ˢ y → Rˢ j′ r′ (intoˢ r′ y) x
≅ˢ-sym z≅      = z≅
≅ˢ-sym (s≅ le e)  = s≅ (≅ᴵ-sym le) (≅ˢ-sym e)
≅ˢ-sym (l≅ h)  = l≅ (λ n → ≅ˢ-sym (h n))
≅ˢ-sym (lᵢ≅ {p = p} {q = q} e h) = lᵢ≅ (≅ᴵ-sym e) (λ y x d → ≅ˢ-sym (h x y (R-flipˢ (<→◃ q) (<→◃ p) d)))
≅ˢ-sym (upˡ {r = zero} e)    = upʳ (≅ˢ-sym e)
≅ˢ-sym (upˡ {r = self n} e)  = upʳ (≅ˢ-sym e)
≅ˢ-sym (upʳ {r = zero} e)    = upˡ (≅ˢ-sym e)
≅ˢ-sym (upʳ {r = self n} e)  = upˡ (≅ˢ-sym e)
≅ˢ-sym (ŝ≅ k ec et eg) = ŝ≅ (sym k) (≅ᴵ-sym ec) (≅ˢ-sym et) (λ η e η′ e′ eη → ≅ˢ-sym (eg η′ e′ η e (≅ᴵ-sym eη)))
≅ˢ-sym (ĉ≅ ec dt dg eo eO) = ĉ≅ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
                               (≅ˢ-sym eo) (λ η e η′ e′ eη → ≅ˢ-sym (eO η′ e′ η e (≅ᴵ-sym eη)))
R-flipˢ zero      r′ e = flipRˢ r′ e
R-flipˢ (suc r)   r′ e = R-flipˢ r r′ e
R-flipˢ (self n)  r′ e = flipRˢ r′ e
R-flipˢ (lim n r) r′ e = R-flipˢ r r′ e
flipRˢ zero       e = ≅ˢ-sym e
flipRˢ (suc r′)   e = flipRˢ r′ e
flipRˢ (self n)   e = ≅ˢ-sym e
flipRˢ (lim n r′) e = flipRˢ r′ e
```

```agda
trˢ-≅    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordˢ ℓ′} → x ≅ˢ y → trˢ e x ≅ˢ y
tr⁻ˢ-≅   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordˢ ℓ′} → x ≅ˢ y → tr⁻ˢ e x ≅ˢ y
backˢ-≅  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordˢ ℓ′} → u ≅ˢ v → backˢ (resˢ q e) u ≅ˢ v
back⁻ˢ-≅ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordˢ ℓ′} → u ≅ˢ v → backˢ (res⁻ˢ q e) u ≅ˢ v

trˢ-≅ e z≅      = z≅
trˢ-≅ e (s≅ le d)  = s≅ (≅ᴵ-trans (≅ᴵ-sym e) le) (trˢ-≅ e d)
trˢ-≅ e (l≅ h)  = l≅ (λ n → trˢ-≅ e (h n))
trˢ-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ≅ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-≅ e (h _ v (≅→Rˢ (<→◃ q) (backˢ-≅ q e (R→≅ˢ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (trˢ-≅ e d)
trˢ-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (trˢ-≅ (h n) d)
trˢ-≅ e (upʳ d) = upʳ (trˢ-≅ e d)
trˢ-≅ e (ŝ≅ k ec et eg) = ŝ≅ (trans (sym (kd-≅ e)) k) ec (trˢ-≅ e et) (λ η d η′ d′ eη → trˢ-≅ e (eg η d η′ d′ eη))
trˢ-≅ e (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (trˢ-≅ e eo) (λ η d η′ d′ eη → trˢ-≅ e (eO η d η′ d′ eη))

tr⁻ˢ-≅ e z≅      = z≅
tr⁻ˢ-≅ e (s≅ le d)  = s≅ (≅ᴵ-trans e le) (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ e (l≅ h)  = l≅ (λ n → tr⁻ˢ-≅ e (h n))
tr⁻ˢ-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ≅ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-≅ e (h _ v (≅→Rˢ (<→◃ q) (back⁻ˢ-≅ q e (R→≅ˢ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻ˢ-≅ (h n) d)
tr⁻ˢ-≅ e (upʳ d) = upʳ (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ e (ŝ≅ k ec et eg) = ŝ≅ (trans (kd-≅ e) k) ec (tr⁻ˢ-≅ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (eg η d η′ d′ eη))
tr⁻ˢ-≅ e (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (tr⁻ˢ-≅ e eo) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (eO η d η′ d′ eη))

backˢ-≅ zero      (s≅ e) d = tr⁻ˢ-≅ e d
backˢ-≅ (suc q)   (s≅ e) d = backˢ-≅ q e d
backˢ-≅ (lim n q) (l≅ h) d = backˢ-≅ q (h n) d

back⁻ˢ-≅ zero      (s≅ e) d = trˢ-≅ e d
back⁻ˢ-≅ (suc q)   (s≅ e) d = back⁻ˢ-≅ q e d
back⁻ˢ-≅ (lim n q) (l≅ h) d = back⁻ˢ-≅ q (h n) d
```

```agda
≅ˢ-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} {c : Ordˢ ℓ₃} → a ≅ˢ b → b ≅ˢ c → a ≅ˢ c
R-reflˡˢ  : ∀ {j ℓ ℓ′} (r : j ◃ ℓ) {x : Ordˢ j} {z : Ordˢ ℓ′} → Rˢ j r (intoˢ r x) z → x ≅ˢ x
≅ˢ-trans (upˡ {r = zero} e)   d = upˡ (≅ˢ-trans e d)
≅ˢ-trans (upˡ {r = self n} e) d = upˡ (≅ˢ-trans e d)
≅ˢ-trans d (upʳ {r = zero} e)   = upʳ (≅ˢ-trans d e)
≅ˢ-trans d (upʳ {r = self n} e) = upʳ (≅ˢ-trans d e)
≅ˢ-trans (upʳ {r = zero} e)   (upˡ e′) = ≅ˢ-trans e e′
≅ˢ-trans (upʳ {r = self n} e) (upˡ e′) = ≅ˢ-trans e e′
≅ˢ-trans z≅     z≅      = z≅
≅ˢ-trans (s≅ le e) (s≅ le′ e′) = s≅ (≅ᴵ-trans le le′) (≅ˢ-trans e e′)
≅ˢ-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅ˢ-trans (h n) (h′ n))
≅ˢ-trans (lᵢ≅ {p = p} {q = q} e h) (lᵢ≅ e′ h′) =
  lᵢ≅ (≅ᴵ-trans e e′) λ x z d →
    ≅ˢ-trans (h x (trˢ e x) (≅→Rˢ (<→◃ p) (≅ˢ-sym (trˢ-≅ e (R-reflˡˢ (<→◃ p) d)))))
             (h′ (trˢ e x) z (≅→Rˢ (<→◃ q) (trˢ-≅ e (R→≅ˢ (<→◃ p) d))))
≅ˢ-trans (ŝ≅ k ec et eg) (ŝ≅ k′ ec′ et′ eg′) =
  ŝ≅ (trans k k′) (≅ᴵ-trans ec ec′) (≅ˢ-trans et et′)
     (λ η e η″ e″ eη → ≅ˢ-trans (eg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (eg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
≅ˢ-trans (ĉ≅ ec dt dg eo eO) (ĉ≅ ec′ dt′ dg′ eo′ eO′) =
  ĉ≅ (≅ᴵ-trans ec ec′) (≅ᶻ-trans dt dt′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
     (≅ˢ-trans eo eo′)
     (λ η e η″ e″ eη → ≅ˢ-trans (eO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (eO′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
R-reflˡˢ zero      e = ≅ˢ-trans e (≅ˢ-sym e)
R-reflˡˢ (suc r)   e = R-reflˡˢ r e
R-reflˡˢ (self n)  e = ≅ˢ-trans e (≅ˢ-sym e)
R-reflˡˢ (lim n r) e = R-reflˡˢ r e

≅ˢ-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → a ≅ˢ a
≅ˢ-reflˡ e = ≅ˢ-trans e (≅ˢ-sym e)

≅ˢ-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → b ≅ˢ b
≅ˢ-reflʳ e = ≅ˢ-trans (≅ˢ-sym e) e

≅-trˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ a} → y ≅ˢ x → y ≅ˢ trˢ e x
≅-trˢ e d = ≅ˢ-sym (trˢ-≅ e (≅ˢ-sym d))

≅-tr⁻ˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ b} → y ≅ˢ x → y ≅ˢ tr⁻ˢ e x
≅-tr⁻ˢ e d = ≅ˢ-sym (tr⁻ˢ-≅ e (≅ˢ-sym d))

Ωˢ-≅ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ≅ˢ Ωˢ b
Ωˢ-≅ z≅     = s≅ z≅ z≅
Ωˢ-≅ (s≅ e) = lᵢ≅ e (λ x y d → upˡ (upʳ d))
Ωˢ-≅ (l≅ h) = l≅ (λ n → upˡ (upʳ (Ωˢ-≅ (h n))))

Ωˢ-refl : ∀ a → Ωˢ a ≅ˢ Ωˢ a
Ωˢ-refl a = Ωˢ-≅ (≅ᴵ-refl a)

toZ-≅ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → toZ x ≅ᶻ toZ y
toZ-≅ z≅     = zᶻ
toZ-≅ (s≅ _ d) = sᶻ (toZ-≅ d)
toZ-≅ (l≅ h) = lᶻ (λ n → toZ-≅ (h n))
toZ-≅ (lᵢ≅ {p = ()} e h)
toZ-≅ (upˡ {r = ()} d)
toZ-≅ (upʳ {r = ()} d)
toZ-≅ (ŝ≅ k ec et eg) = ĉᶻ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη))
                           (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη))
toZ-≅ (ĉ≅ ec dt dg eo eO) = ĉᶻ ec dt dg (toZ-≅ eo) (λ η e η′ e′ eη → toZ-≅ (eO η e η′ e′ eη))

addˢ-≅ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordˢ ℓ₂} {b : Ordˢ k₁} {b′ : Ordˢ k₂} →
         ℓ₁ ≅ᴵ ℓ₂ → a ≅ˢ a′ → b ≅ˢ b′ → addˢ a σ b ≅ˢ addˢ a′ σ′ b′
addˢ-≅ kℓ ea z≅     = ea
addˢ-≅ kℓ ea (s≅ _ e) = s≅ kℓ (addˢ-≅ kℓ ea e)
addˢ-≅ kℓ ea (l≅ h) = l≅ (λ n → addˢ-≅ kℓ ea (h n))
addˢ-≅ kℓ ea (upˡ {r = zero} e)   = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upˡ {r = self n} e) = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upʳ {r = zero} e)   = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upʳ {r = self n} e) = addˢ-≅ kℓ ea e
addˢ-≅ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} kℓ ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ≅ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ≅ˢ addˢ a′ σ′ (g (intoˢ (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-intoˢ (<→◃ (σ′ q′)) y))
         (addˢ-≅ kℓ ea (h x y (R-convˢ (<→◃ (σ q)) (<→◃ q) d)))
addˢ-≅ {k₁ = zero}    {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = zero}    {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ {k₁ = zero}    {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ {k₁ = suc _}   {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ {k₁ = lim _ _} {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ {k₁ = suc _}   {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ kℓ) ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = suc _}   {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ kℓ) ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = lim _ _} {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ kℓ) ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = lim _ _} {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ kℓ) ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ kℓ ea (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (addˢ-≅ kℓ ea eo) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eO η e η′ e′ eη))
s-invˢ : ∀ {k k′} {a : Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.suc a ≅ˢ Ord₊ˢ.suc b → a ≅ˢ b
s-invˢ (s≅ _ e) = e

l-invˢ : ∀ {k k′} {f : ℕ → Ordˢ k} {g : ℕ → Ordˢ k′} → Ord₊ˢ.lim f ≅ˢ Ord₊ˢ.lim g → ∀ n → f n ≅ˢ g n
l-invˢ (l≅ h) = h

i-respˢ : ∀ {k k′ j} {p : j <ᴵ k} {f : Uˢ j (<→◃ p) → Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.limᵢ p f ≅ˢ b →
          ∀ {z z′ : Ordˢ j} → z ≅ˢ z′ → f (intoˢ (<→◃ p) z) ≅ˢ f (intoˢ (<→◃ p) z′)
i-respˢ {p = p} (lᵢ≅ e h) {z} {z′} d =
  ≅ˢ-trans (h z (trˢ e z′) (≅→Rˢ (<→◃ p) (≅-trˢ e d)))
           (≅ˢ-sym (h z′ (trˢ e z′) (≅→Rˢ (<→◃ p) (≅-trˢ e (≅ˢ-reflʳ d)))))
i-respˢ (upʳ {r = zero} e)   = i-respˢ e
i-respˢ (upʳ {r = self n} e) = i-respˢ e

u-invˢ : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} {b : Ordˢ ℓ′} → Ord₊ˢ.up r x ≅ˢ b → outˢ (◃₁→◃ r) x ≅ˢ b
u-invˢ zero     (upˡ e)              = e
u-invˢ zero     (upʳ {r = zero} e)   = upʳ (u-invˢ zero e)
u-invˢ zero     (upʳ {r = self n} e) = upʳ (u-invˢ zero e)
u-invˢ (self m) (upˡ e)              = e
u-invˢ (self m) (upʳ {r = zero} e)   = upʳ (u-invˢ (self m) e)
u-invˢ (self m) (upʳ {r = self n} e) = upʳ (u-invˢ (self m) e)

u-reflˢ : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} → Ord₊ˢ.up r x ≅ˢ Ord₊ˢ.up r x → outˢ (◃₁→◃ r) x ≅ˢ outˢ (◃₁→◃ r) x
u-reflˢ r e = ≅ˢ-reflˡ (u-invˢ r e)

ŝ-refl₀ : ∀ {k k′ c t₀ g} {b : Ordˢ k′} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ≅ˢ b → t₀ ≅ˢ t₀
ŝ-refl₀ (ŝ≅ _ _ et _)        = ≅ˢ-reflˡ et
ŝ-refl₀ (upʳ {r = zero} e)   = ŝ-refl₀ e
ŝ-refl₀ (upʳ {r = self n} e) = ŝ-refl₀ e

ĉ-refl₀ : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b → o₀ ≅ˢ o₀
ĉ-refl₀ (ĉ≅ _ _ _ eo _)      = ≅ˢ-reflˡ eo
ĉ-refl₀ (upʳ {r = zero} e)   = ĉ-refl₀ e
ĉ-refl₀ (upʳ {r = self n} e) = ĉ-refl₀ e

self-trˢ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → x ≅ˢ x → trˢ e x ≅ˢ trˢ e x
self-trˢ e d = ≅ˢ-reflˡ (trˢ-≅ e (≅-trˢ e d))

self-tr⁻ˢ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → x ≅ˢ x → tr⁻ˢ e x ≅ˢ tr⁻ˢ e x
self-tr⁻ˢ e d = ≅ˢ-reflˡ (tr⁻ˢ-≅ e (≅-tr⁻ˢ e d))

ĉ-reflg : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b → ∀ η e → o η e ≅ˢ o η e
ĉ-reflg (ĉ≅ ec _ _ _ eO) η e     = ≅ˢ-reflˡ (eO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η))
ĉ-reflg (upʳ {r = zero} d) η e   = ĉ-reflg d η e
ĉ-reflg (upʳ {r = self n} d) η e = ĉ-reflg d η e
```

## §2 深度 0 的折叠

```agda
infix 4 _≈ᴿ_
_≈ᴿ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴿ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ˢ R′ ev′ p′

limR : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴿ G n) → limA 0 F ≈ᴿ limA 0 G
limR h ev p ev′ p′ ei = l≅ (λ n → h n ev p ev′ p′ ei)

sucR : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴿ R′ → sucRun R ≈ᴿ sucRun R′
sucR h ev p ev′ p′ ei = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ ei (h ev p ev′ p′ ei) e′) z≅)

limᵢR : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
        {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
        j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → H x ≈ᴿ H′ y) → limᵢA 0 ac H ≈ᴿ limᵢA 0 ac′ H′
limᵢR {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → H (tr⁻ˢ e₁ u) ev p ≅ˢ H′ (tr⁻ˢ e₂ v) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)

ĉR : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
     {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
     O₀ ≈ᴿ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈ᴿ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴿ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉR ec dt dg h₀ h ev p ev′ p′ ei = ĉ≅ ec dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

ŝR : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     c ≅ᴵ c′ → T₀ ≈ᴿ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᴿ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴿ ŝA 0 c′ T₀′ G′
ŝR ec h₀ h ev p ev′ p′ ei = ŝ≅ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

cloR : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
       {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
       t ≈ᴿ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴿ g′ η′) → cloA 0 t g ≈ᴿ cloA 0 t′ g′
cloR {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)

wkR : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
      R ≈ᴿ R′ → wk 0 le R ≈ᴿ wk 0 le′ R′
wkR le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei
```
