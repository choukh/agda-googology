# 值判据 (零): 值序, 无记号世界

> **判决: HOLDS (底座).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). `≼` 与 [OCFSpecBase](OCFSpecBase.lagda.md) §1 的构造子逐字相同, 差别只是树取自 `OCF.Free.Level`: 证书主线 (`LadderInf*`) 的树就在那里, `OCF.Align.Level` 是另一份类型. 多了: 结构序到值序的桥 `≺→≺ᵛ`, `⊑→≼`. 这个文件的导入闭包只有 `OCF.Free.Level` 与 stdlib.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)

open import OCF.Free.Level

𝟎 : ∀ {ℓ} → Ordᶜ ℓ
𝟎 = zero

infix 4 _≼_ _≈ᵛ_ _≺ᵛ_

data _≼_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  z≼  : ∀ {ℓ₁ ℓ₂} {b : Ordᶜ ℓ₂} → 𝟎 {ℓ₁} ≼ b
  s≼s : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → suc a ≼ suc b
  ≼l  : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ≼ f n → a ≼ lim f
  l≼  : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ≼ b) → lim f ≼ b
  ≼i  : ∀ {ℓ₁ ℓ₂ j} {a : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
        (x : Ordᶜ j) → x ≅ x → a ≼ f (into (<→◃ p) x) → a ≼ limᵢ p f
  i≼  : ∀ {ℓ₁ ℓ₂ j} {p : j <ᴵ ℓ₁} {f : U j (<→◃ p) → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} →
        (∀ (x : Ordᶜ j) → x ≅ x → f (into (<→◃ p) x) ≼ b) → limᵢ p f ≼ b
  ≼u  : ∀ {ℓ₁ ℓ₂ k} {a : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → a ≼ out (◃₁→◃ r) y → a ≼ up r y
  u≼  : ∀ {ℓ₁ ℓ₂ k} {r : k ◃₁ ℓ₁} {y : U k (◃₁→◃ r)} {b : Ordᶜ ℓ₂} → out (◃₁→◃ r) y ≼ b → up r y ≼ b

≼-refl : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≼ a
≼-refl zero            = z≼
≼-refl (suc a)         = s≼s (≼-refl a)
≼-refl (lim f)         = l≼ (λ n → ≼l n (≼-refl (f n)))
≼-refl (limᵢ p f)      = i≼ (λ x ex → ≼i x ex (≼-refl (f (into (<→◃ p) x))))
≼-refl (up zero y)     = u≼ (≼u (≼-refl y))
≼-refl (up (self n) y) = u≼ (≼u (≼-refl y))

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼          q           = z≼
≼-trans p           (≼l n q)    = ≼l n (≼-trans p q)
≼-trans p           (≼i x ex q) = ≼i x ex (≼-trans p q)
≼-trans p           (≼u q)      = ≼u (≼-trans p q)
≼-trans (l≼ p)      q           = l≼ (λ n → ≼-trans (p n) q)
≼-trans (i≼ p)      q           = i≼ (λ x ex → ≼-trans (p x ex) q)
≼-trans (u≼ p)      q           = u≼ (≼-trans p q)
≼-trans (s≼s p)     (s≼s q)     = s≼s (≼-trans p q)
≼-trans (≼l n p)    (l≼ q)      = ≼-trans p (q n)
≼-trans (≼i x ex p) (i≼ q)      = ≼-trans p (q x ex)
≼-trans (≼u p)      (u≼ q)      = ≼-trans p q

_≈ᵛ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ≈ᵛ b = a ≼ b × b ≼ a

_≺ᵛ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ≺ᵛ b = suc a ≼ b

≼-suc : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → a ≼ suc b
≼-suc z≼                          = z≼
≼-suc (s≼s p)                     = s≼s (≼-suc p)
≼-suc (≼l {f = f} n p)            = ≼-trans (≼-suc p) (s≼s (≼l n (≼-refl (f n))))
≼-suc (l≼ p)                      = l≼ (λ n → ≼-suc (p n))
≼-suc (≼i {p = q} {f = f} x ex p) = ≼-trans (≼-suc p) (s≼s (≼i x ex (≼-refl (f (into (<→◃ q) x)))))
≼-suc (i≼ p)                      = i≼ (λ x ex → ≼-suc (p x ex))
≼-suc (≼u {r = r} {y = y} p)      = ≼-trans (≼-suc p) (s≼s (≼u (≼-refl (out (◃₁→◃ r) y))))
≼-suc (u≼ p)                      = u≼ (≼-suc p)

≼-self-suc : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≼ suc a
≼-self-suc a = ≼-suc (≼-refl a)

≺→≼ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ᵛ b → a ≼ b
≺→≼ p = ≼-trans (≼-self-suc _) p

s≼s⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → suc a ≼ suc b → a ≼ b
s≼s⁻ (s≼s p) = p

≼lim⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} → suc a ≼ lim f → Σ ℕ (λ n → suc a ≼ f n)
≼lim⁻ (≼l n p) = n , p

≺-≼ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≺ᵛ b → b ≼ c → a ≺ᵛ c
≺-≼ = ≼-trans

≼-≺ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≼ b → b ≺ᵛ c → a ≺ᵛ c
≼-≺ p q = ≼-trans (s≼s p) q

≅→≼ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≼ b
≅→≼ z≅      = z≼
≅→≼ (s≅ e)  = s≼s (≅→≼ e)
≅→≼ (l≅ h)  = l≼ (λ n → ≼l n (≅→≼ (h n)))
≅→≼ (lᵢ≅ {p = p} e h) =
  i≼ (λ x ex → ≼i (tr e x) (tr-≅ e (≅-tr e ex)) (≅→≼ (h x (tr e x) (≅→R (<→◃ p) (≅-tr e ex)))))
≅→≼ (upˡ {r = zero} e)   = u≼ (≅→≼ e)
≅→≼ (upˡ {r = self n} e) = u≼ (≅→≼ e)
≅→≼ (upʳ {r = zero} e)   = ≼u (≅→≼ e)
≅→≼ (upʳ {r = self n} e) = ≼u (≅→≼ e)

≅→≈ᵛ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≈ᵛ b
≅→≈ᵛ e = ≅→≼ e , ≅→≼ (≅-sym e)

data Acc {k} (a : Ordᶜ k) : Set where
  acc : (∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → Acc ξ) → Acc a

acc-≼ : ∀ {k m} {x : Ordᶜ k} {y : Ordᶜ m} → x ≼ y → Acc y → Acc x
acc-≼ p (acc h) = acc (λ ξ q → h ξ (≼-trans q p))

wf    : ∀ {k} (a : Ordᶜ k) → Acc a
belowᵛ : ∀ {k} (a : Ordᶜ k) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → Acc ξ
wf a = acc (belowᵛ a)
belowᵛ (suc b)         ξ (s≼s p)   = acc-≼ p (wf b)
belowᵛ (lim f)         ξ (≼l n q)  = belowᵛ (f n) ξ q
belowᵛ (limᵢ p f)      ξ (≼i x e q) = belowᵛ (f (into (<→◃ p) x)) ξ q
belowᵛ (up zero y)     ξ (≼u q)    = belowᵛ y ξ q
belowᵛ (up (self n) y) ξ (≼u q)    = belowᵛ y ξ q

≺ᵛ-irrefl : ∀ {k} (a : Ordᶜ k) → ¬ (a ≺ᵛ a)
≺ᵛ-irrefl a = go (wf a) where
  go : ∀ {k} {a : Ordᶜ k} → Acc a → ¬ (a ≺ᵛ a)
  go {a = a} (acc h) q = go (h a q) q

≺→s≼ : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≺ b → suc c ≼ b
≺→s≼ (≺z e)      = s≼s (≅→≼ e)
≺→s≼ (≺s h)      = ≼-suc (≺→s≼ h)
≺→s≼ (≺l n h)    = ≼l n (≺→s≼ h)
≺→s≼ (≺i x ex h) = ≼i x ex (≺→s≼ h)
≺→s≼ (≺u h)      = ≼u (≺→s≼ h)

⊑→≼ : ∀ {ℓ₂} (a : Ordᶜ zero) {b : Ordᶜ ℓ₂} → a ⊑ b → a ≼ b
⊑→≼ zero        k = z≼
⊑→≼ (suc a)     k = ≺→s≼ (k (≺z (≅-refl⁰ a)))
⊑→≼ (lim f)     k = l≼ (λ n → ⊑→≼ (f n) (λ h → k (≺l n h)))
⊑→≼ (limᵢ () f) k
⊑→≼ (up () x)   k

-- 一个点列的严格上确界: 严格上界, 共尾
≼lim : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ≼ f n → a ≼ lim f
≼lim = ≼l
```
