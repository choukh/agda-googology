# 有向关系的统一闭包与实际全有限地板

证明按树与关系本身递归；不要求任意raw树自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformClosure where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionUniformIf
import OCF.Lean.BoundedMixedAffine as A
import OCF.Align.BoundedCompletionTerminalValueIf as TV
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)

prefix-rel : ∀ {S Q a b} → TreeValue S Q a b → ∀ c → TreeValue S Q a (b ⊞ c)
prefix-rel p hz = p
prefix-rel p (hs c) = vr (prefix-rel p c)
prefix-rel p (hl f) = vli 0 (prefix-rel p (f 0))
prefix-rel p (hΩ κ g) = vor (λ c → prefix-rel p (g c))
right-rel : ∀ {S Q} (a : HB S) {b c} → TreeValue S Q b c → TreeValue S Q b (a ⊞ c)
right-rel a vz = vz
right-rel a (vs p) = vs (right-rel a p)
right-rel a (vr p) = vr (right-rel a p)
right-rel a (vl p) = vl (λ n → right-rel a (p n))
right-rel a (vli n p) = vli n (right-rel a p)
right-rel a (vo p) = vo (λ x y r → right-rel a (p x y r))
right-rel a (vor p) = vor (λ c → right-rel a (p c))
add-rel : ∀ {S Q a b c d} → TreeValue S Q a b → TreeValue S Q c d →
  TreeValue S Q (a ⊞ c) (b ⊞ d)
add-rel p vz = prefix-rel p _
add-rel p (vs q) = vs (add-rel p q)
add-rel p (vr q) = vr (add-rel p q)
add-rel p (vl q) = vl (λ n → add-rel p (q n))
add-rel p (vli n q) = vli n (add-rel p q)
add-rel p (vo q) = vo (λ x y r → add-rel p (q x y r))
add-rel p (vor q) = vor (λ c → add-rel p (q c))
partial-rel : ∀ {S Q a b} → TreeValue S Q a b → ∀ n →
  TreeValue S Q (Ops.partial S (λ _ → a) n) (Ops.partial S (λ _ → b) n)
partial-rel p zero = p
partial-rel p (suc n) = add-rel (partial-rel p n) p
repeat-rel : ∀ {S Q a b} → TreeValue S Q a b →
  TreeValue S Q (Ops.repeat S a) (Ops.repeat S b)
repeat-rel p = vl (λ n → vli n (partial-rel p n))

same-right : ∀ {S Q a b c} → TreeValue S Q a b → Same b c → TreeValue S Q a c
same-right vz q = vz
same-right (vs p) (ss q) = vs (same-right p q)
same-right (vr p) (ss q) = vr (same-right p q)
same-right (vl p) q = vl (λ n → same-right (p n) q)
same-right (vli n p) (ll q) = vli n (same-right p (q n))
same-right (vo p) (oo q) = vo (λ x y r → same-right (p x y r) (q y))
same-right (vor p) (oo q) = vor (λ c → same-right (p c) (q c))

pure-up : ∀ {a b : Cd} → a ≤ᵛ b → Value hz (up a) (up b)
pure-up z≤ = vz
pure-up (s≤s p) = vs (pure-up p)
pure-up (≤s p) = vr (pure-up p)
pure-up (l≤ p) = vl (λ n → pure-up (p n))
pure-up (≤l n p) = vli n (pure-up p)
up-value : ∀ c {a b} → Value c a b → Value (hs c) (up a) (up b)
up-value c vz = vz
up-value c (vs p) = vs (up-value c p)
up-value c (vr p) = vr (up-value c p)
up-value c (vl p) = vl (λ n → up-value c (p n))
up-value c (vli n p) = vli n (up-value c p)
up-value c (vo p) = vo (λ x y r → up-value c (p x y r))
up-value c (vor p) = vor (λ d → up-value c (p d))

floor-value : ∀ n → Value (num n) (floor n) (floor n)
floor-value zero = vo (λ x y p → pure-up p)
floor-value (suc n) = vo (λ x y p → up-value (num n) p)

value-zero : ∀ {a b} → Value hz a b → TV.VRel a b
value-zero vz = TV.vz
value-zero (vs p) = TV.vs (value-zero p)
value-zero (vr p) = TV.vr (value-zero p)
value-zero (vl p) = TV.vl (λ n → value-zero (p n))
value-zero (vli n p) = TV.vli n (value-zero p)
value-zero (vo {κ = inj₁ ()} p)
value-zero (vo {κ = inj₂ _} p) = TV.vo (λ r → value-zero (p _ _ r))
value-zero (vor {κ = inj₁ ()} p)
value-zero (vor {κ = inj₂ _} p) = TV.vor (λ c → value-zero (p c))

module Affine (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) where
  module Act = A.Action S (hs hz)
  positive : ∀ a → TreeValue S Q (hs hz) (Act.run a)
  positive hz = vs vz
  positive (hs a) = vli 0 (positive a)
  positive (hl f) = vli 0 (positive (f 0))
  positive (hΩ κ g) = vor (λ c → positive (g c))
  mono : ∀ {a b} → TreeValue S Q a b → TreeValue S Q (Act.run a) (Act.run b)
  mono {b = b} vz = positive b
  mono (vs p) = repeat-rel (mono p)
  mono (vr p) = vli 0 (mono p)
  mono (vl p) = vl (λ n → mono (p n))
  mono (vli n p) = vli n (mono p)
  mono (vo p) = vo (λ x y r → mono (p x y r))
  mono (vor p) = vor (λ c → mono (p c))
  inflate : ∀ {a b} → TreeValue S Q a b → TreeValue S Q a (Act.run b)
  inflate vz = vz
  inflate {b = hs b} (vs p) = vli 1 (add-rel (inflate p) (positive b))
  inflate (vr p) = vli 0 (inflate p)
  inflate (vl p) = vl (λ n → inflate (p n))
  inflate (vli n p) = vli n (inflate p)
  inflate (vo p) = vo (λ x y r → inflate (p x y r))
  inflate (vor p) = vor (λ c → inflate (p c))
```
