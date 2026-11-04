> **机械克隆, 验收用.** 由 `OrdLabZRelative` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZRelative where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.EmbVVOZPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; trˢ; tr⁻ˢ; addˢ; Restrˢ; resˢ; res⁻ˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁)
open import OCF.Align.EmbVVOZGoodLBase using (LabL)
open import OCF.Align.EmbVVOZUniformS
```

```agda
open Ord-Ord using (iter)
open Restrˢ using (repˢ; backˢ; ltˢ; eqˢ)
open E using (T; natT; Ωt) renaming (ψ to ψᵗ)
```

## §2 层对齐的互模拟 $\cong^\mathsf A$

```agda
data UpK : ∀ {k k′ ℓ ℓ′} → k ◃₁ ℓ → k′ ◃₁ ℓ′ → Set where
  uz : ∀ {k k′} → UpK (zero {k}) (zero {k′})
  us : ∀ {f g : ℕ → Ordᴵ} {s t} n → UpK (self {f} {s} n) (self {g} {t} n)

module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set) where
  data Eqᴬ : ∀ {ℓ′} → Ordˢ ℓ → Ordˢ ℓ′ → Set where
    zᴬ  : ∀ {ℓ′} → Eqᴬ {ℓ′} Ord₊ˢ.zero Ord₊ˢ.zero
    sᴬ  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordˢ ℓ′} → Eqᴬ a b → Eqᴬ (Ord₊ˢ.suc a) (Ord₊ˢ.suc b)
    lᴬ  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eqᴬ (f n) (g n)) → Eqᴬ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lᵢᴬ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : Uˢ j′ (<→◃ q) → Ordˢ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordˢ j′) → R j (<→◃ p) (intoˢ (<→◃ p) x) y → Eqᴬ (f (intoˢ (<→◃ p) x)) (g (intoˢ (<→◃ q) y))) →
          Eqᴬ (Ord₊ˢ.limᵢ p f) (Ord₊ˢ.limᵢ q g)
    uᴬ  : ∀ {ℓ′ k k′} {r : k ◃₁ ℓ} {r′ : k′ ◃₁ ℓ′} {x : Uˢ k (◃₁→◃ r)} {y : Uˢ k′ (◃₁→◃ r′)} →
          UpK r r′ → R k (◃₁→◃ r) x (outˢ (◃₁→◃ r′) y) → Eqᴬ (Ord₊ˢ.up r x) (Ord₊ˢ.up r′ y)
    ŝᴬ  : ∀ {ℓ′ c c′} {t₀ : Ordˢ ℓ} {t₀′ : Ordˢ ℓ′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          kd ℓ ≡ kd ℓ′ → c ≅ᴵ c′ → Eqᴬ t₀ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eqᴬ (g η e) (g′ η′ e′)) →
          Eqᴬ (Ord₊ˢ.ŝ c t₀ g) (Ord₊ˢ.ŝ c′ t₀′ g′)
    ĉᴬ  : ∀ {ℓ′ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
          {o₀ : Ordˢ ℓ} {o₀′ : Ordˢ ℓ′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
          Eqᴬ o₀ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eqᴬ (o η e) (o′ η′ e′)) →
          Eqᴬ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (Ord₊ˢ.ĉᴸ c′ t₀′ g′ o₀′ o′)

Rᴬ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set
Rᴬ i zero         x b = Eqᴬ i Rᴬ x b
Rᴬ i (suc r)      x b = Rᴬ i r x b
Rᴬ _ (self {f} n) x b = Eqᴬ (f n) Rᴬ x b
Rᴬ i (lim n r)    x b = Rᴬ i r x b

infix 4 _≅ᴬ_
_≅ᴬ_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordˢ ℓ₂ → Set
_≅ᴬ_ {ℓ₁} = Eqᴬ ℓ₁ Rᴬ

R→≅ᴬ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → Rᴬ i r (intoˢ r x) b → x ≅ᴬ b
R→≅ᴬ zero      e = e
R→≅ᴬ (suc r)   e = R→≅ᴬ r e
R→≅ᴬ (self n)  e = e
R→≅ᴬ (lim n r) e = R→≅ᴬ r e

≅→Rᴬ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → x ≅ᴬ b → Rᴬ i r (intoˢ r x) b
≅→Rᴬ zero      e = e
≅→Rᴬ (suc r)   e = ≅→Rᴬ r e
≅→Rᴬ (self n)  e = e
≅→Rᴬ (lim n r) e = ≅→Rᴬ r e
```

```agda
≅ᴬ-sym  : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ᴬ b → b ≅ᴬ a
R-flipᴬ : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → Rᴬ j r (intoˢ r x) y → Rᴬ j′ r′ (intoˢ r′ y) x
flipRᴬ  : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → x ≅ᴬ y → Rᴬ j′ r′ (intoˢ r′ y) x
≅ᴬ-sym zᴬ = zᴬ
≅ᴬ-sym (sᴬ d) = sᴬ (≅ᴬ-sym d)
≅ᴬ-sym (lᴬ h) = lᴬ (λ n → ≅ᴬ-sym (h n))
≅ᴬ-sym (lᵢᴬ {p = p} {q = q} e h) = lᵢᴬ (≅ᴵ-sym e) (λ y x d → ≅ᴬ-sym (h x y (R-flipᴬ (<→◃ q) (<→◃ p) d)))
≅ᴬ-sym (uᴬ uz d) = uᴬ uz (≅ᴬ-sym d)
≅ᴬ-sym (uᴬ (us n) d) = uᴬ (us n) (≅ᴬ-sym d)
≅ᴬ-sym (ŝᴬ k ec et eg) = ŝᴬ (sym k) (≅ᴵ-sym ec) (≅ᴬ-sym et) (λ η e η′ e′ eη → ≅ᴬ-sym (eg η′ e′ η e (≅ᴵ-sym eη)))
≅ᴬ-sym (ĉᴬ ec dt dg eo eO) = ĉᴬ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
                               (≅ᴬ-sym eo) (λ η e η′ e′ eη → ≅ᴬ-sym (eO η′ e′ η e (≅ᴵ-sym eη)))
R-flipᴬ zero      r′ e = flipRᴬ r′ e
R-flipᴬ (suc r)   r′ e = R-flipᴬ r r′ e
R-flipᴬ (self n)  r′ e = flipRᴬ r′ e
R-flipᴬ (lim n r) r′ e = R-flipᴬ r r′ e
flipRᴬ zero       e = ≅ᴬ-sym e
flipRᴬ (suc r′)   e = flipRᴬ r′ e
flipRᴬ (self n)   e = ≅ᴬ-sym e
flipRᴬ (lim n r′) e = flipRᴬ r′ e

≅ᴬ→≅ˢ₀ : ∀ {ℓ′} {x : Ordˢ zero} {y : Ordˢ ℓ′} → x ≅ᴬ y → x ≅ˢ y
≅ᴬ→≅ˢ₀ zᴬ = z≅
≅ᴬ→≅ˢ₀ (sᴬ d) = s≅ (≅ᴬ→≅ˢ₀ d)
≅ᴬ→≅ˢ₀ (lᴬ h) = l≅ (λ n → ≅ᴬ→≅ˢ₀ (h n))
≅ᴬ→≅ˢ₀ (lᵢᴬ {p = ()} e h)
≅ᴬ→≅ˢ₀ (uᴬ {r = ()} k d)
≅ᴬ→≅ˢ₀ (ŝᴬ k ec et eg) = ŝ≅ k ec (≅ᴬ→≅ˢ₀ et) (λ η e η′ e′ eη → ≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))
≅ᴬ→≅ˢ₀ (ĉᴬ ec dt dg eo eO) = ĉ≅ ec dt dg (≅ᴬ→≅ˢ₀ eo) (λ η e η′ e′ eη → ≅ᴬ→≅ˢ₀ (eO η e η′ e′ eη))
```

```agda
trˢ-≅ᴬ    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordˢ ℓ′} → x ≅ᴬ y → trˢ e x ≅ᴬ y
tr⁻ˢ-≅ᴬ   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordˢ ℓ′} → x ≅ᴬ y → tr⁻ˢ e x ≅ᴬ y
backˢ-≅ᴬ  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordˢ ℓ′} → u ≅ᴬ v → backˢ (resˢ q e) u ≅ᴬ v
back⁻ˢ-≅ᴬ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordˢ ℓ′} → u ≅ᴬ v → backˢ (res⁻ˢ q e) u ≅ᴬ v

trˢ-≅ᴬ e zᴬ = zᴬ
trˢ-≅ᴬ e (sᴬ d) = sᴬ (trˢ-≅ᴬ e d)
trˢ-≅ᴬ e (lᴬ h) = lᴬ (λ n → trˢ-≅ᴬ e (h n))
trˢ-≅ᴬ e (lᵢᴬ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ≅ᴬ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-≅ᴬ e (h _ v (≅→Rᴬ (<→◃ q) (backˢ-≅ᴬ q e (R→≅ᴬ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-≅ᴬ (s≅ e) (uᴬ uz d) = uᴬ uz (trˢ-≅ᴬ e d)
trˢ-≅ᴬ (l≅ h) (uᴬ (us n) d) = uᴬ (us n) (trˢ-≅ᴬ (h n) d)
trˢ-≅ᴬ e (ŝᴬ k ec et eg) = ŝᴬ (trans (sym (kd-≅ e)) k) ec (trˢ-≅ᴬ e et) (λ η d η′ d′ eη → trˢ-≅ᴬ e (eg η d η′ d′ eη))
trˢ-≅ᴬ e (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (trˢ-≅ᴬ e eo) (λ η d η′ d′ eη → trˢ-≅ᴬ e (eO η d η′ d′ eη))

tr⁻ˢ-≅ᴬ e zᴬ = zᴬ
tr⁻ˢ-≅ᴬ e (sᴬ d) = sᴬ (tr⁻ˢ-≅ᴬ e d)
tr⁻ˢ-≅ᴬ e (lᴬ h) = lᴬ (λ n → tr⁻ˢ-≅ᴬ e (h n))
tr⁻ˢ-≅ᴬ e (lᵢᴬ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ≅ᴬ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-≅ᴬ e (h _ v (≅→Rᴬ (<→◃ q) (back⁻ˢ-≅ᴬ q e (R→≅ᴬ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-≅ᴬ (s≅ e) (uᴬ uz d) = uᴬ uz (tr⁻ˢ-≅ᴬ e d)
tr⁻ˢ-≅ᴬ (l≅ h) (uᴬ (us n) d) = uᴬ (us n) (tr⁻ˢ-≅ᴬ (h n) d)
tr⁻ˢ-≅ᴬ e (ŝᴬ k ec et eg) = ŝᴬ (trans (kd-≅ e) k) ec (tr⁻ˢ-≅ᴬ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ᴬ e (eg η d η′ d′ eη))
tr⁻ˢ-≅ᴬ e (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (tr⁻ˢ-≅ᴬ e eo) (λ η d η′ d′ eη → tr⁻ˢ-≅ᴬ e (eO η d η′ d′ eη))

backˢ-≅ᴬ zero      (s≅ e) d = tr⁻ˢ-≅ᴬ e d
backˢ-≅ᴬ (suc q)   (s≅ e) d = backˢ-≅ᴬ q e d
backˢ-≅ᴬ (lim n q) (l≅ h) d = backˢ-≅ᴬ q (h n) d

back⁻ˢ-≅ᴬ zero      (s≅ e) d = trˢ-≅ᴬ e d
back⁻ˢ-≅ᴬ (suc q)   (s≅ e) d = back⁻ˢ-≅ᴬ q e d
back⁻ˢ-≅ᴬ (lim n q) (l≅ h) d = back⁻ˢ-≅ᴬ q (h n) d

≅ᴬ-tr⁻ˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ b} → y ≅ᴬ x → y ≅ᴬ tr⁻ˢ e x
≅ᴬ-tr⁻ˢ e d = ≅ᴬ-sym (tr⁻ˢ-≅ᴬ e (≅ᴬ-sym d))

Ωˢ-≅ᴬ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ≅ᴬ Ωˢ b
Ωˢ-≅ᴬ z≅     = sᴬ zᴬ
Ωˢ-≅ᴬ (s≅ e) = lᵢᴬ e (λ x y d → uᴬ uz d)
Ωˢ-≅ᴬ (l≅ h) = lᴬ (λ n → uᴬ (us n) (Ωˢ-≅ᴬ (h n)))
```

```agda
R-convᴬ : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordˢ j} {b : Ordˢ ℓ′} → Rᴬ j r (intoˢ r x) b → Rᴬ j r′ (intoˢ r′ x) b
R-convᴬ r r′ e = ≅→Rᴬ r′ (R→≅ᴬ r e)

addˢ-≅ᴬ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordˢ ℓ₂} {b : Ordˢ k₁} {b′ : Ordˢ k₂} →
          kd ℓ₁ ≡ kd ℓ₂ → a ≅ᴬ a′ → b ≅ᴬ b′ → addˢ a σ b ≅ᴬ addˢ a′ σ′ b′
addˢ-≅ᴬ kℓ ea zᴬ     = ea
addˢ-≅ᴬ kℓ ea (sᴬ e) = sᴬ (addˢ-≅ᴬ kℓ ea e)
addˢ-≅ᴬ kℓ ea (lᴬ h) = lᴬ (λ n → addˢ-≅ᴬ kℓ ea (h n))
addˢ-≅ᴬ kℓ ea (uᴬ uz e)     = addˢ-≅ᴬ kℓ ea e
addˢ-≅ᴬ kℓ ea (uᴬ (us n) e) = addˢ-≅ᴬ kℓ ea e
addˢ-≅ᴬ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} kℓ ea (lᵢᴬ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢᴬ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ≅ᴬ addˢ a′ σ′ (g (intoˢ (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-intoˢ (<→◃ (σ′ q′)) y))
         (addˢ-≅ᴬ kℓ ea (h x y (R-convᴬ (<→◃ (σ q)) (<→◃ q) d)))
addˢ-≅ᴬ {k₁ = zero}    {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) =
  ĉᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (addˢ-≅ᴬ kℓ ea et)
     (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = zero}    {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ᴬ {k₁ = zero}    {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ kℓ ea (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (addˢ-≅ᴬ kℓ ea eo) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eO η e η′ e′ eη))
```

## §6 结论与边界
