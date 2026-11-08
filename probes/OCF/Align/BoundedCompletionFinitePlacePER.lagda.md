# 已准入结构关系的对称与传递

Rel不对全部raw树自反；只从已经相关的一对树取得各自自相关。
这允许组合实际跨注入证明，不把关系当作Agda等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlacePER where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (same-sym)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure using (pure-reflexive)

rel-sym : ∀ c {a b} → Rel c a b → Rel c b a
coord-sym : ∀ c κ {a b} → Coord c κ a b → Coord c κ b a
rel-sym c rz = rz
rel-sym c (rs p) = rs (rel-sym c p)
rel-sym c (rl p) = rl (λ n → rel-sym c (p n))
rel-sym c (ro {κ = κ} p) = ro (λ x y r → rel-sym c (p y x (coord-sym c κ r)))
coord-sym hz (inj₁ ()) r
coord-sym hz (inj₂ _) r = same-sym r
coord-sym (hs c) (inj₁ κ) r = coord-sym c κ r
coord-sym (hs c) (inj₂ _) r = rel-sym c r
coord-sym (hl f) (n , κ) r = coord-sym (f n) κ r

rel-trans : ∀ c {a b d} → Rel c a b → Rel c b d → Rel c a d
coord-left : ∀ c κ {a b} → Coord c κ a b → Coord c κ a a
rel-trans c rz rz = rz
rel-trans c (rs p) (rs q) = rs (rel-trans c p q)
rel-trans c (rl p) (rl q) = rl (λ n → rel-trans c (p n) (q n))
rel-trans c (ro {κ = κ} p) (ro q) = ro
  (λ x y r → rel-trans c (p x x (coord-left c κ r)) (q x y r))
coord-left hz (inj₁ ()) r
coord-left hz (inj₂ _) {a} r = pure-reflexive a
coord-left (hs c) (inj₁ κ) r = coord-left c κ r
coord-left (hs c) (inj₂ _) r = rel-trans c r (rel-sym c r)
coord-left (hl f) (n , κ) r = coord-left (f n) κ r

rel-left : ∀ c {a b} → Rel c a b → Rel c a a
rel-left c p = rel-trans c p (rel-sym c p)
```
