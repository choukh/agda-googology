# Level (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Level](../../Align/Level.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Level where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans) 
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level public
```

```agda
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open Ord-Ord using (iter; ordᴰ)

```

## §4 树族、层间搬运与折叠

```agda

coe : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) → U i r → U i r′
coe r r′ x = into r′ (out r x)

lift : ∀ {k ℓ} → k ◃ ℓ → Ordᶜ k → Ordᶜ ℓ
lift zero      x = up zero x
lift (suc r)   x = up zero (lift r x)
lift (self n)  x = up (self n) x
lift (lim n r) x = up (self n) (lift r x)
```

```agda
open Restr
```

```agda
Ω : (ℓ : Ordᴵ) → Ordᶜ ℓ
Ω zero      = suc zero
Ω (suc ℓ)   = limᵢ zero (up zero)
Ω (lim f s) = lim (λ n → up (self n) (Ω (f n)))

add : ∀ {k ℓ} → Ordᶜ ℓ → Simᴵ k ℓ → Ordᶜ k → Ordᶜ ℓ
add a σ zero              = a
add a σ (suc b)           = suc (add a σ b)
add a σ (lim f)           = lim (λ n → add a σ (f n))
add a σ (limᵢ q f)        = limᵢ (σ q) (λ y → add a σ (f (coe (<→◃ (σ q)) (<→◃ q) y)))
add a σ (up zero x)       = add a (λ q → σ (suc q)) x
add a σ (up (self n) x)   = add a (λ q → σ (lim n q)) x

infixl 6 _+_
_+_ : ∀ {ℓ} → Ordᶜ ℓ → Ordᶜ ℓ → Ordᶜ ℓ
a + b = add a (λ q → q) b

ψ : ∀ {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → Ordᶜ k → Ordᶜ i
ψ p σ zero    = Ω _
ψ p σ (suc a) = lim (iter (ψ p σ a +_) zero)
ψ p σ (lim f) = lim (λ n → ψ p σ (f n))
ψ p σ (limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = limᵢ r (λ y → ψ p σ (f (into (<→◃ q) (tr⁻ e (out (<→◃ r) y)))))
... | injᵇ _ = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
... | injᶜ _ = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ p σ (up zero x)     = ψ p (λ q → σ (suc q)) x
ψ p σ (up (self n) x) = ψ p (λ q → σ (lim n q)) x

ψ⁰ : ∀ {k} → Ordᶜ k → Ordᶜ zero
ψ⁰ zero    = suc zero
ψ⁰ (suc a) = lim (iter (ψ⁰ a +_) zero)
ψ⁰ (lim f) = lim (λ n → ψ⁰ (f n))
ψ⁰ (limᵢ {i = j} q f) = lim (λ n → ψ⁰ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ⁰ (up zero x)     = ψ⁰ x
ψ⁰ (up (self n) x) = ψ⁰ x
```

## §5 跨层结构互模拟 $\cong$

```agda

R-conv : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordᶜ j} {b : Ordᶜ ℓ′} → R j r (into r x) b → R j r′ (into r′ x) b
R-conv r r′ e = ≅→R r′ (R→≅ r e)
```

```agda
≅-tr⁻ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ b} → y ≅ x → y ≅ tr⁻ e x
≅-tr⁻ e d = ≅-sym (tr⁻-≅ e (≅-sym d))
```

```agda
Ω-≅ : ∀ {a b} → a ≅ᴵ b → Ω a ≅ Ω b
Ω-≅ z≅     = s≅ z≅
Ω-≅ (s≅ e) = lᵢ≅ e (λ x y d → upˡ (upʳ d))
Ω-≅ (l≅ h) = l≅ (λ n → upˡ (upʳ (Ω-≅ (h n))))

Ω-refl : ∀ ℓ → Ω ℓ ≅ Ω ℓ
Ω-refl ℓ = Ω-≅ (≅ᴵ-refl ℓ)

lift-≅ : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {x : Ordᶜ k} {b : Ordᶜ ℓ′} → x ≅ b → lift r x ≅ b
lift-≅ zero      e = upˡ e
lift-≅ (suc r)   e = upˡ (lift-≅ r e)
lift-≅ (self n)  e = upˡ e
lift-≅ (lim n r) e = upˡ (lift-≅ r e)
```

## §6 折叠尊重 $\cong$

```agda
add-≅ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordᶜ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordᶜ k₁} {b′ : Ordᶜ k₂} →
        a ≅ a′ → b ≅ b′ → add a σ b ≅ add a′ σ′ b′
add-≅ ea z≅     = ea
add-≅ ea (s≅ e) = s≅ (add-≅ ea e)
add-≅ ea (l≅ h) = l≅ (λ n → add-≅ ea (h n))
add-≅ ea (upˡ {r = zero} e)   = add-≅ ea e
add-≅ ea (upˡ {r = self n} e) = add-≅ ea e
add-≅ ea (upʳ {r = zero} e)   = add-≅ ea e
add-≅ ea (upʳ {r = self n} e) = add-≅ ea e
add-≅ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ≅ e λ x y d →
  subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ≅ add a′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-into (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
         (add-≅ ea (h x y (R-conv (<→◃ (σ q)) (<→◃ q) d)))

ψ-≅ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {a : Ordᶜ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ≅ b → ψ p σ a ≅ ψ p′ σ′ b
ψ-≅ ei z≅ = Ω-≅ ei
ψ-≅ ei (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ-≅ ei e) e′) z≅)
ψ-≅ ei (l≅ h) = l≅ (λ n → ψ-≅ ei (h n))
ψ-≅ ei (upˡ {r = zero} e)   = ψ-≅ ei e
ψ-≅ ei (upˡ {r = self n} e) = ψ-≅ ei e
ψ-≅ ei (upʳ {r = zero} e)   = ψ-≅ ei e
ψ-≅ ei (upʳ {r = self n} e) = ψ-≅ ei e
ψ-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u))) ≅ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
         (sym (out-into (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
         (ψ-≅ ei (h _ _ (≅→R (<→◃ q) (tr⁻-≅ e₁ (≅-tr⁻ e₂ (R→≅ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
```

```agda
ψ⁰-≅ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ⁰ b
ψ⁰-≅ z≅     = s≅ z≅
ψ⁰-≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰-≅ e) e′) z≅)
ψ⁰-≅ (l≅ h) = l≅ (λ n → ψ⁰-≅ (h n))
ψ⁰-≅ (upˡ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upˡ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ (lᵢ≅ {p = q} e h) = l≅ (λ n → ψ⁰-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)

ψ⁰≅ψ : ∀ {k₁ k₂ ℓ} {p : zero <ᴵ ℓ} {σ : Simᴵ k₂ ℓ} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ p σ b
ψ⁰≅ψ z≅     = s≅ z≅
ψ⁰≅ψ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰≅ψ e) e′) z≅)
ψ⁰≅ψ (l≅ h) = l≅ (λ n → ψ⁰≅ψ (h n))
ψ⁰≅ψ (upˡ {r = zero} e)   = ψ⁰≅ψ e
ψ⁰≅ψ (upˡ {r = self n} e) = ψ⁰≅ψ e
ψ⁰≅ψ (upʳ {r = zero} e)   = ψ⁰≅ψ e
ψ⁰≅ψ (upʳ {r = self n} e) = ψ⁰≅ψ e
ψ⁰≅ψ {p = p} {σ = σ} (lᵢ≅ {p = q} {q = q′} e h) with <ᴵ-dec (σ q′) p
... | injᵃ (via _ ())
... | injᵇ _ = l≅ (λ n → ψ⁰≅ψ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ = l≅ (λ n → ψ⁰≅ψ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
```

## §7 叶子为 $\cong$ 的结构序

```agda

≺-respˡ : ∀ {ℓ₁ ℓ₁′ ℓ₂} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₁′} {b : Ordᶜ ℓ₂} → c ≅ c′ → c ≺ b → c′ ≺ b
≺-respˡ e (≺z e′)      = ≺z (≅-trans (≅-sym e) e′)
≺-respˡ e (≺s h)       = ≺s (≺-respˡ e h)
≺-respˡ e (≺l n h)     = ≺l n (≺-respˡ e h)
≺-respˡ e (≺i x ex h)  = ≺i x ex (≺-respˡ e h)
≺-respˡ e (≺u h)       = ≺u (≺-respˡ e h)
```

## §8 $\Omega$ 与 $\psi\circ\Omega$ 的单调性

```agda
𝟎 : ∀ {ℓ} → Ordᶜ ℓ
𝟎 = zero
```

## §12 结论与边界
