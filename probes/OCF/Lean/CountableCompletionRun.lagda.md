# 累加完成的实际实例与无条件值下界

直接使用已有CRw.leg，未改动它或原下降运行器。合法性对所有raw树
成立；值下界按树结构证明，不从增长率推序数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CountableCompletionRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.CountableCompletionIf

right-add : ∀ (a b : Cd) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))

item-sum : ∀ (f : ℕ → Cd) n → f n ≤ᵛ Σ₀ f n
item-sum f zero = ≤-refl _
item-sum f (suc n) = right-add _ _

inflation : ∀ (a : Cd) → a ≤ᵛ leg a
inflation hz = z≤
inflation (hs a) = s≤s (inflation a)
inflation (hl f) = l≤ (λ n → ≤l n
  (≤-trans (inflation (f n)) (item-sum (λ k → leg (f k)) n)))

instance-completion : Completion
instance-completion = record
  { complete = leg
  ; lawful = Lg-leg
  ; lower = inflation }
```

完成可以提高值，未证明统一上界或保持原值。不能把本篇当成原raw
输出的合法性证明，也不能据此把完成后的候选命名为ψ₀Λ。
