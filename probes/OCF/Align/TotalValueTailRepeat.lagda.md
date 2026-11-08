# 完成对真实极限重复的严格增值

这里分析末端完成本身，不更改运行器。对任意正的根极限树，
其 ω 重复经完成后严格增值。这排除把「已经取累计极限」当作
完成幂等的充分理由；不声称最高闭项一定落在本定理的形状中。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailRepeat where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
import OCF.Free.LiteralCompletion as C
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans; ≤⊞; ⊞≤ˡ; ⊞≤ʳ; mul≤)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.TotalValueTailUpper using (lower; item)

repeat : Cd → Cd
repeat a = hl (mul a)

add-mono : ∀ {a b c d : Cd} → a ≤ᵛ b → c ≤ᵛ d → a ⊞ c ≤ᵛ b ⊞ d
add-mono {b = b} p q = ≤ᵛ-trans (⊞≤ˡ _ p) (⊞≤ʳ b q)
repeat-mono : ∀ {a b} → a ≤ᵛ b → repeat a ≤ᵛ repeat b
repeat-mono p = l≤ (λ n → ≤l n (mul≤ p n))

-- 完成后仍保留任意左前缀，不用把原值关系穿过 leg。
prefix : ∀ (p a : Cd) → C.leg p ≤ᵛ C.leg (p ⊞ a)
prefix p hz = ≤ᵛ-refl _
prefix p (hs a) = ≤s (prefix p a)
prefix p (hl f) = ≤l zero (prefix p (f zero))
prefix p (hΩ () g)

prefix-sums : ∀ (p : Cd) (f : ℕ → Cd) n →
  mul (C.leg p) n ≤ᵛ C.Σ₀ (λ k → C.leg (p ⊞ f k)) n
prefix-sums p f zero = prefix p (f zero)
prefix-sums p f (suc n) = add-mono (prefix-sums p f n) (prefix p (f (suc n)))

prefix-repeat : ∀ (p : Cd) (f : ℕ → Cd) →
  repeat (C.leg p) ≤ᵛ C.leg (p ⊞ hl f)
prefix-repeat p f = l≤ (λ n → ≤l n (prefix-sums p f n))

-- 两次真正的左前缀吸收，选取完成列的第三项。
double-repeat : ∀ (f : ℕ → Cd) →
  repeat (repeat (hl f)) ≤ᵛ C.leg (repeat (hl f))
double-repeat f = ≤l (suc (suc zero)) (≤ᵛ-trans
  (≤ᵛ-trans (repeat-mono (≤ᵛ-trans (repeat-mono (lower (hl f)))
    (prefix-repeat (hl f) f))) (prefix-repeat (mul (hl f) (suc zero)) f))
  (item (λ n → C.leg (mul (hl f) n)) (suc (suc zero))))

positive-repeat : ∀ a → hs hz ≤ᵛ a → hs hz ≤ᵛ repeat a
positive-repeat a p = ≤l zero p
strict-repeat : ∀ (f : ℕ → Cd) → hs hz ≤ᵛ hl f →
  hs (repeat (hl f)) ≤ᵛ C.leg (repeat (hl f))
strict-repeat f p = ≤ᵛ-trans
  (≤l (suc zero) (⊞≤ʳ (repeat (hl f)) (positive-repeat (hl f) p)))
  (double-repeat f)

not-preserved : ∀ (f : ℕ → Cd) → hs hz ≤ᵛ hl f →
  C.leg (repeat (hl f)) ≤ᵛ repeat (hl f) → ⊥
not-preserved f p q = ¬s≤ᵛ (repeat (hl f)) (≤ᵛ-trans (strict-repeat f p) q)
```
