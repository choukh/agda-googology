# 原up跨源层的完整观察模拟

左目标m≤n，右源提高到n+1而保留同一个目标m。Ω的两条反馈链只需
低层Rel，不需高层raw Same自相关；异坐标枝证据逐次由输入ro提供。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteRelUp where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.GeneralOmegaFiniteRelIf
open import OCF.Lean.GeneralOmegaFiniteRelRun

node-raise : ∀ {n m A} (Q : A → A → Set) (p : Within n m) (v : View n m A) → Good Q v →
  (rec : ∀ k → Within n k → A → HB (F k)) →
  (rec′ : ∀ k → Within (suc n) k → A → HB (F k)) →
  (∀ k q {a b} → Q a b → Rel k (rec k q a) (rec′ k (lower q) b)) →
  Rel m (node p v rec) (node (lower p) (raise v) rec′)
node-raise Q p (keep κ fr) good rec rec′ rel = ro (λ r → rel _ p (good r))
node-raise Q p (collapse k q to) good rec rec′ rel = rl (λ i → rel _ p
  (good (iterate-rel (λ r → rel k q (good r)) (floor-related k) i)))

up-observe : ∀ {n m a b} (p : Within n m) → Rel n a b →
  Rel m (observe p a) (observe (lower p) (up b))
up-observe {m = m} p rz = floor-related m
up-observe p (rs r) = rl (left-rel (up-observe p r))
up-observe p (rl r) = rl (λ i → up-observe p (r i))
up-observe {n} p (ro {κ} {f} {g} r) = node-raise (Coord n κ) p (view p κ) (view-good p κ)
  (λ k q e → observe q (f e)) (λ k q e → observe q (up (g e)))
  (λ k q cd → up-observe q (r cd))
```

定理没有改变原up/observer。它不处理目标m大于未嵌入source n的情况；
这种Read递归须保留原ambient source和嵌入证据，不能偷写Within n m。
