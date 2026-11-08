# 原累计地板的全部异层同形证书

每个原kind按同形高度匹配，Ω枝只消费相应低层Tree；并层地板
保留全部ΣT前缀，逐项采用同一个原Nat分量编号。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeFloor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (rawΓ; Γ)
open import OCF.Lean.GeneralOmegaCountableShapeIf
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)

add-tree : ∀ {S T k Q x y u v} → HTrees S T k Q x y → HTrees S T k Q u v → HTrees S T k Q (x ⊞ u) (y ⊞ v)
add-tree p tz = p
add-tree p (ts q) = ts (add-tree p q)
add-tree p (tl q) = tl (λ n → add-tree p (q n))
add-tree p (to q) = to (λ r → add-tree p (q r))
node-eq : ∀ {S T k Q κ j f g} (eq : j ≡ k κ) →
  (∀ {x y} → Q κ x (subst (E T) eq y) → HTrees S T k Q (f x) (g y)) →
  HTrees S T k Q (hΩ κ f) (hΩ j g)
node-eq refl r = to r
change : ∀ {S T k k′ Q Q′} (eq : ∀ κ → k κ ≡ k′ κ)
  (back : ∀ κ x y → Q′ κ x (subst (E T) (eq κ) y) → Q κ x y)
  {a b} → HTrees S T k Q a b → HTrees S T k′ Q′ a b
change eq back tz = tz
change eq back (ts p) = ts (change eq back p)
change eq back (tl p) = tl (λ n → change eq back (p n))
change eq back (to {κ} p) = node-eq (eq κ) (λ r → change eq back (p (back κ _ _ r)))

module Lift (S T : KS) (k : K S → K T) (Q : ∀ κ → E S κ → E T (k κ) → Set) where
  keys : K (step S) → K (step T)
  keys (inj₁ κ) = inj₁ (k κ)
  keys (inj₂ u) = inj₂ u
  coords : ∀ κ → E (step S) κ → E (step T) (keys κ) → Set
  coords (inj₁ κ) = Q κ
  coords (inj₂ _) = HTrees S T k Q
  trees : ∀ {x y} → HTrees S T k Q x y → HTrees (step S) (step T) keys coords (up x) (up y)
  trees tz = tz
  trees (ts p) = ts (trees p)
  trees (tl p) = tl (λ n → trees (p n))
  trees (to p) = to (λ r → trees (p r))
module Up {a b : Cd} (p : Same a b) where
  module L = Lift (F a) (F b) (map-K p) (Coord p)
  keys : ∀ κ → L.keys κ ≡ map-K (ss p) κ
  keys (inj₁ κ) = refl
  keys (inj₂ u) = refl
  coords : ∀ κ x y → Coord (ss p) κ x (subst (E (F (hs b))) (keys κ) y) → L.coords κ x y
  coords (inj₁ κ) x y r = r
  coords (inj₂ u) x y r = r
  trees : ∀ {x y} → Tree p x y → Tree (ss p) (up x) (up y)
  trees r = change {S = step (F a)} {T = step (F b)} {k = L.keys} {k′ = map-K (ss p)} {Q = L.coords} {Q′ = Coord (ss p)} keys coords (L.trees r)
up-tree : ∀ {a b : Cd} (p : Same a b) {x y} → Tree p x y → Tree (ss p) (up x) (up y)
up-tree p = Up.trees p

module Sum (S T : ℕ → KS) (k : ∀ n → K (S n) → K (T n))
  (Q : ∀ n κ → E (S n) κ → E (T n) (k n κ) → Set) where
  keys : K (sup ℕ S) → K (sup ℕ T)
  keys (n , κ) = n , k n κ
  coords : ∀ κ → E (sup ℕ S) κ → E (sup ℕ T) (keys κ) → Set
  coords (n , κ) = Q n κ
  trees : ∀ n {x y} → HTrees (S n) (T n) (k n) (Q n) x y →
    HTrees (sup ℕ S) (sup ℕ T) keys coords (ι n x) (ι n y)
  trees n tz = tz
  trees n (ts p) = ts (trees n p)
  trees n (tl p) = tl (λ i → trees n (p i))
  trees n (to p) = to (λ r → trees n (p r))
module Iota {f g : ℕ → Cd} (p : ∀ n → Same (f n) (g n)) where
  module L = Sum (λ n → F (f n)) (λ n → F (g n)) (λ n → map-K (p n)) (λ n → Coord (p n))
  keys : ∀ κ → L.keys κ ≡ map-K (ll p) κ
  keys (n , κ) = refl
  coords : ∀ κ x y → Coord (ll p) κ x (subst (E (F (hl g))) (keys κ) y) → L.coords κ x y
  coords (n , κ) x y r = r
  trees : ∀ n {x y} → Tree (p n) x y → Tree (ll p) (ι n x) (ι n y)
  trees n r = change {S = F (hl f)} {T = F (hl g)} {k = L.keys} {k′ = map-K (ll p)} {Q = L.coords} {Q′ = Coord (ll p)} keys coords (L.trees n r)
iota-tree : ∀ {f g : ℕ → Cd} (p : ∀ n → Same (f n) (g n)) n {x y} →
  Tree (p n) x y → Tree (ll p) (ι n x) (ι n y)
iota-tree p = Iota.trees p
floor-tree : ∀ {a b : Cd} (p : Same a b) → Tree p (floor a) (floor b)
sums-tree : ∀ {f g : ℕ → Cd} (p : ∀ n → Same (f n) (g n)) n →
  Tree (ll p) (C.ΣT S⊥ (hs hz) f n) (C.ΣT S⊥ (hs hz) g n)
floor-tree zz = ts tz
floor-tree (ss p) = to (λ r → up-tree p r)
floor-tree (ll p) = tl (sums-tree p)
floor-tree (oo {κ = ()} p)
sums-tree p zero = iota-tree p zero (floor-tree (p zero))
sums-tree p (suc n) = add-tree (sums-tree p n) (iota-tree p (suc n) (floor-tree (p (suc n))))

Γ-input-tree : ∀ {a b : Cd} (p : Same a b) → Tree (leg-same p) (floor (leg a)) (floor (leg b))
Γ-input-tree p = floor-tree (leg-same p)
from-observer : CanonicalObserverShape → GammaShape
from-observer obs = record
  { preserve-Γ = λ p → leg-same (CanonicalObserverShape.preserve obs p (Γ-input-tree p)) }
```

Γ-input-tree给任意原Same高度的真实完整Γ输入，无限制为有限层。
from-observer准确列出剩余运行器字段：canonical观察保持还未由本篇
证明，不能把地板Tree证书自身读作Γ值相容或终点大小。
