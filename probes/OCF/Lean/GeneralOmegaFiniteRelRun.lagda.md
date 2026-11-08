# 原分类、原反馈迭代保持遗传关系

keep只反向运输当前目标坐标关系；collapse从自己的低层Rel取坐标。
无累加迭代始于相关原floor，回调的异坐标关系来自源ro证书，不从
普通Same推断任意分支同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteRelRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)
open import OCF.Lean.GeneralOmegaFiniteRelIf

add-rel : ∀ {n a b c d} → Rel n a b → Rel n c d → Rel n (a ⊞ c) (b ⊞ d)
add-rel p rz = p
add-rel p (rs q) = rs (add-rel p q)
add-rel p (rl q) = rl (λ i → add-rel p (q i))
add-rel p (ro q) = ro (λ r → add-rel p (q r))
up-rel : ∀ {n a b} → Rel n a b → Rel (suc n) (up a) (up b)
up-rel rz = rz
up-rel (rs p) = rs (up-rel p)
up-rel (rl p) = rl (λ i → up-rel (p i))
up-rel (ro p) = ro (λ r → up-rel (p r))
floor-related : ∀ n → Rel n (floor n) (floor n)
floor-related zero = rs rz
floor-related (suc n) = ro (λ p → up-rel p)
left-rel : ∀ {n a b} → Rel n a b → ∀ i → Rel n (leftMul a i) (leftMul b i)
left-rel p zero = rz
left-rel p (suc i) = add-rel p (left-rel p i)
iterate-rel : ∀ {n} {f g : HB (F n) → HB (F n)} →
  (∀ {a b} → Rel n a b → Rel n (f a) (g b)) → ∀ {a b} → Rel n a b →
  ∀ i → Rel n (iterate f a i) (iterate g b i)
iterate-rel fg p zero = p
iterate-rel fg p (suc i) = fg (iterate-rel fg p i)

Good : ∀ {n m A} → (A → A → Set) → View n m A → Set
Good {m = m} Q (keep κ fr) = ∀ {a b} → Coord m κ a b → Q (fr a) (fr b)
Good Q (collapse k p to) = ∀ {a b} → Rel k a b → Q (to a) (to b)
view-good : ∀ {n m} (p : Within n m) κ → Good (Coord n κ) (view p κ)
view-good here κ r = r
view-good (lower p) (inj₁ κ) with view p κ | view-good p κ
... | keep κ′ fr | g = g
... | collapse k q to | g = g
view-good (lower p) (inj₂ _) r = r

node-rel : ∀ {n m A} (Q : A → A → Set) (p : Within n m) (v : View n m A) → Good Q v →
  (rec rec′ : ∀ k → Within n k → A → HB (F k)) →
  (∀ k q {a b} → Q a b → Rel k (rec k q a) (rec′ k q b)) →
  Rel m (node p v rec) (node p v rec′)
node-rel Q p (keep κ fr) good rec rec′ rel = ro (λ r → rel _ p (good r))
node-rel Q p (collapse k q to) good rec rec′ rel = rl (λ i → rel _ p
  (good (iterate-rel (λ r → rel k q (good r)) (floor-related k) i)))

observe-related : ∀ {n m a b} (p : Within n m) → Rel n a b → Rel m (observe p a) (observe p b)
observe-related {m = m} p rz = floor-related m
observe-related p (rs r) = rl (left-rel (observe-related p r))
observe-related p (rl r) = rl (λ i → observe-related p (r i))
observe-related {n} p (ro {κ} {f} {g} r) = node-rel (Coord n κ) p (view p κ) (view-good p κ)
  (λ k q e → observe q (f e)) (λ k q e → observe q (g e))
  (λ k q cd → observe-related q (r cd))
instance-rel : RelObserver
instance-rel = record { floor-related = floor-related ; observe-related = observe-related }
```

本定理保持同一个Within路径，不假两条路径证明无关。原floor全n
已实填输入证书；跨source的up模拟与可数值结论另给。
