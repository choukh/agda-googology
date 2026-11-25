# YiXVFiniteCanonicalInputs
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteCanonicalInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBridge as E
import OCF.Lean.YiXVFiniteCoerce as C

module At (n m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n)) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  good-in : ∀ X → A.Gd m X → D.GU q (L.into (L.<→◃ q) X)
  good-in X gx = subst (λ X → X) (sym (E.GU-eq n m q L.zero X)) gx
  good-out : ∀ u → D.GU q u → A.Gd m (L.out (L.<→◃ q) u)
  good-out u gu = subst (λ X → X) (E.GU-eq n m q L.zero (L.out (L.<→◃ q) u))
    (subst (D.GU q) (sym (C.into-out (L.<→◃ q) u)) gu)
  rel-in : ∀ X Y → A.Le m X Y → D.RU q (L.into (L.<→◃ q) X) (L.into (L.<→◃ q) Y)
  rel-in X Y p = subst (λ X → X) (sym (E.RU-eq n m q L.zero X Y)) p
  rel-out : ∀ u v → D.RU q u v → A.Le m (L.out (L.<→◃ q) u) (L.out (L.<→◃ q) v)
  rel-out u v p = subst (λ X → X) (E.RU-eq n m q L.zero (L.out (L.<→◃ q) u) (L.out (L.<→◃ q) v))
    (subst (λ X → D.RU q (L.into (L.<→◃ q) (L.out (L.<→◃ q) u)) X) (sym (C.into-out (L.<→◃ q) v))
      (subst (λ X → D.RU q X v) (sym (C.into-out (L.<→◃ q) u)) p))
  floor-in : ∀ X → A.Le m (L.Ω (L.natᴵ m)) X → D.Floor q (L.into (L.<→◃ q) X)
  floor-in X p = subst (λ X → X) (sym (E.floor-eq n m q L.zero X)) p
  floor-out : ∀ u → D.Floor q u → A.Le m (L.Ω (L.natᴵ m)) (L.out (L.<→◃ q) u)
  floor-out u p = subst (λ X → X) (E.floor-eq n m q L.zero (L.out (L.<→◃ q) u))
    (subst (D.Floor q) (sym (C.into-out (L.<→◃ q) u)) p)

actual : A.Gd 1 (L.out (L.<→◃ (L.suc L.zero)) (L.Ω (L.natᴵ 1)))
actual = At.good-out 2 1 (L.suc L.zero) (L.Ω (L.natᴵ 1))
  (At.good-in 2 1 (L.suc L.zero) (L.Ω (L.natᴵ 1)) A.actual₁)
```
