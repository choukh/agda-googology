# 严格列: Brouwer 序

> 入口 [TLCode](TLCode.lagda.md). 与 [LadderOrdCode](LadderOrdCode.lagda.md) §1, [LadderOrdStr](LadderOrdStr.lagda.md) 开头相同, 只为让本路的主线不导入 `Code`. 只用于陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeLe where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _≅ᴵ_; _≺ᴵ_; via; _⊑ᴵ_; z≅; s≅; l≅)

infix 4 _≼_
data _≼_ : Ordᴵ → Ordᴵ → Set where
  z≼  : ∀ {b} → zero ≼ b
  s≼  : ∀ {a b} → a ≼ b → suc a ≼ suc b
  s≼ʳ : ∀ {a b} → a ≼ b → a ≼ suc b
  l≼  : ∀ {f s b} → (∀ n → f n ≼ b) → lim f s ≼ b
  l≼ʳ : ∀ {a f s} n → a ≼ f n → a ≼ lim f s

≼-refl : ∀ a → a ≼ a
≼-refl zero = z≼
≼-refl (suc a) = s≼ (≼-refl a)
≼-refl (lim f s) = l≼ (λ n → l≼ʳ n (≼-refl (f n)))

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼ y = z≼
≼-trans (s≼ x) (s≼ y) = s≼ (≼-trans x y)
≼-trans (s≼ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ x) y)
≼-trans (s≼ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ x) y)
≼-trans (s≼ʳ x) (s≼ y) = s≼ʳ (≼-trans x y)
≼-trans (s≼ʳ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ʳ x) y)
≼-trans (s≼ʳ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ʳ x) y)
≼-trans (l≼ h) y = l≼ (λ n → ≼-trans (h n) y)
≼-trans (l≼ʳ n x) (l≼ h) = ≼-trans x (h n)
≼-trans (l≼ʳ n x) (s≼ʳ y) = s≼ʳ (≼-trans (l≼ʳ n x) y)
≼-trans (l≼ʳ n x) (l≼ʳ k y) = l≼ʳ k (≼-trans (l≼ʳ n x) y)

≅→≼ : ∀ {a b} → a ≅ᴵ b → a ≼ b
≅→≼ z≅ = z≼
≅→≼ (s≅ e) = s≼ (≅→≼ e)
≅→≼ (l≅ h) = l≼ (λ n → l≼ʳ n (≅→≼ (h n)))

<→s≼ : ∀ {a t} → a <ᴵ t → suc a ≼ t
<→s≼ zero = ≼-refl _
<→s≼ (suc q) = s≼ʳ (<→s≼ q)
<→s≼ (lim n q) = l≼ʳ n (<→s≼ q)

≺→s≼ : ∀ {a t} → a ≺ᴵ t → suc a ≼ t
≺→s≼ (via e q) = ≼-trans (s≼ (≅→≼ e)) (<→s≼ q)

≺→≼ : ∀ {a t} → a ≺ᴵ t → a ≼ t
≺→≼ x = ≼-trans (s≼ʳ (≼-refl _)) (≺→s≼ x)

Eqv : Ordᴵ → Ordᴵ → Set
Eqv a b = (a ≼ b) × (b ≼ a)
```
