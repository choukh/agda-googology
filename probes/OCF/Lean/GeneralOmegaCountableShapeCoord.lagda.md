# 实际分类种类的异层坐标运输

只消费同形高度及对应位置，不合并不同路径。种类等式只逐点用于
坐标类型运输；不将函数分支同余作为隐含前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeCoord where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableShapeIf
open import OCF.Lean.GeneralOmegaCountableShapeBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)

ClCoord : ∀ {A B} {p : Same A B} {κ v w} → ClShape p κ v w → Set
ClCoord {p = p} {κ} {C.nw i pi encode} {C.nw j pj encode′} (cnew q h) =
  ∀ {x y} → Tree q x y → Coord p κ (encode x) (encode′ y)
cl-coord : ∀ {A B} (p : Same A B) κ → ClCoord (cl-shape p κ)
cl-coord zz ()
cl-coord {A = hs A} {B = hs B} (ss p) (inj₁ κ)
  with C.cl A κ | C.cl B (map-K p κ) | cl-shape p κ | cl-coord p κ
... | C.nw i pi encode | C.nw j pj encode′ | cnew q h | r = r
cl-coord (ss p) (inj₂ u) r = r
cl-coord {A = hl f} {B = hl g} (ll p) (n , κ)
  with C.cl (f n) κ | C.cl (g n) (map-K (p n) κ) | cl-shape (p n) κ | cl-coord (p n) κ
... | C.nw i pi encode | C.nw j pj encode′ | cnew q h | r = r
cl-coord (oo {κ = ()} p) κ

along-key : ∀ {a b A B} {p : Same a b} {q : Same A B} {u v} →
  Paths (ss p) q u v → C.along v ≡ map-K q (C.along u)
along-key (phere (ss p)) = refl
along-key (pnext h) = cong inj₁ (along-key h)
along-key (plimit n h) = cong (λ κ → n , κ) (along-key h)
old-subst : ∀ {S : KS} {κ κ′ : K S} (e : κ ≡ κ′) (y : E S κ) →
  subst (E (step S)) (cong inj₁ e) y ≡ subst (E S) e y
old-subst refl y = refl
sum-subst : ∀ {S : ℕ → KS} n {κ κ′ : K (S n)} (e : κ ≡ κ′) (y : E (S n) κ) →
  subst (E (sup ℕ S)) (cong (λ κ → n , κ) e) y ≡ subst (E (S n)) e y
sum-subst n refl y = refl
along-coord : ∀ {a b A B} {p : Same a b} {q : Same A B} {u v}
  (h : Paths (ss p) q u v) {x y} →
  Coord q (C.along u) x (subst (E (F B)) (along-key h) y) →
  Tree p (C.frA u x) (C.frA v y)
along-coord (phere (ss p)) r = r
along-coord (pnext {q = q} h) {x} {y} r = along-coord h
  (subst (λ z → Coord q _ x z) (old-subst (along-key h) y) r)
along-coord (plimit {g = g} {q = q} n h) {x} {y} r = along-coord h
  (subst (λ z → Coord (q n) _ x z) (sum-subst {S = λ n → F (g n)} n (along-key h) y) r)
```
