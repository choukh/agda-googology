# 完成的全部部分和进入原回调输出和

原输出和q_n与坐标C_(n+1)的区别是最左种子1。使用强逐形关系处理
这个区别，leg只沿该关系运输，不沿一般值序运输。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCompletionRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.CountableCompletionRun using (right-add)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Lean.GeneralOmegaCompletionIf

data ShapeBelow : Cd → Cd → Set where
  zero : ∀ {b} → ShapeBelow hz b
  successor : ∀ {a b} → ShapeBelow a b → ShapeBelow (hs a) (hs b)
  limit : ∀ {f g} → (∀ n → ShapeBelow (f n) (g n)) → ShapeBelow (hl f) (hl g)

prefix : ∀ b a → ShapeBelow a (b ⊞ a)
prefix b hz = zero
prefix b (hs a) = successor (prefix b a)
prefix b (hl f) = limit (λ n → prefix b (f n))
prefix b (hΩ () f)

right-congruence : ∀ {a b} → ShapeBelow a b → ∀ c → ShapeBelow (a ⊞ c) (b ⊞ c)
right-congruence p hz = p
right-congruence p (hs c) = successor (right-congruence p c)
right-congruence p (hl f) = limit (λ n → right-congruence p (f n))
right-congruence p (hΩ () f)

parts-mono : ∀ {f g : ℕ → Cd} → (∀ n → f n ≤ᵛ g n) → ∀ n →
  Ops.partial S⊥ f n ≤ᵛ Ops.partial S⊥ g n
parts-mono p zero = p zero
parts-mono p (suc n) = add-mono (parts-mono p n) (p (suc n))

Σ-mono : ∀ {f g : ℕ → Cd} → (∀ n → f n ≤ᵛ g n) → ∀ n → Σ₀ f n ≤ᵛ Σ₀ g n
Σ-mono p zero = p zero
Σ-mono p (suc n) = add-mono (Σ-mono p n) (p (suc n))
Σ-partial : ∀ {f g : ℕ → Cd} → (∀ n → f n ≤ᵛ g n) → ∀ n →
  Σ₀ f n ≤ᵛ Ops.partial S⊥ g n
Σ-partial p zero = p zero
Σ-partial p (suc n) = add-mono (Σ-partial p n) (p (suc n))

complete-shape : ∀ {a b} → ShapeBelow a b → leg a ≤ᵛ leg b
complete-shape zero = z≤
complete-shape (successor p) = s≤s (complete-shape p)
complete-shape (limit p) = l≤ (λ n → ≤l n (Σ-mono (λ j → complete-shape (p j)) n))

module Result (H : Cd → Cd) (captured : Capture H) where
  open Capture captured
  output : ℕ → Cd
  output n = H (chain H n)
  q : ℕ → Cd
  q = Ops.partial S⊥ output

  output-shape : ∀ n → ShapeBelow (q n) (chain H (suc n))
  output-shape zero = prefix (hs hz) (output zero)
  output-shape (suc n) = right-congruence (output-shape n) (output (suc n))

  completed-output : ∀ n → leg (q n) ≤ᵛ output (suc n)
  completed-output n = ≤-trans (complete-shape (output-shape n)) (on-chain (suc n))
  completed-sums : ∀ n → Σ₀ (λ j → leg (q j)) n ≤ᵛ
    Ops.partial S⊥ (λ j → output (suc j)) n
  completed-sums n = Σ-partial completed-output n
  shifted-sums : ∀ n → Ops.partial S⊥ (λ j → output (suc j)) n ≤ᵛ q (suc n)
  shifted-sums zero = right-add (output zero) (output 1)
  shifted-sums (suc n) = add-mono (shifted-sums n) (≤-refl _)

  upper : leg (diagonal H H) ≤ᵛ diagonal H H
  upper = l≤ (λ n → ≤l (suc n) (≤-trans (completed-sums n) (shifted-sums n)))

  instance-stable : Stable H
  instance-stable = record { upper = upper }
```

没有H单调、H输出合法或全raw值同余前提。完成的第n部分和进入原
第n+1部分和，比较全部自然数。Capture的真实实例另给，不能仅凭
这个条件定理认定当前完整Λ源raw已完成保值。
