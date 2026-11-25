# YiXVFiniteInputs
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteBridge as E

module At (n : ℕ) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  ref-start : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → I.Uref n q (C.start q) ≡ E.Ω (E.num n q)
  ref-start {i} q = trans (cong (subst L.Ordᶜ (E.eq n q)) (L.out-into (L.<→◃ q) (L.Ω i))) (C.cast-Ω (E.eq n q))
  good-start : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → D.GU q (C.start q)
  good-start q = subst (A.GoFam n (E.idx n q)) (sym (ref-start q)) (proj₁ (B.Ω-model n (E.idx n q)))
  floor-start : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) → D.Floor q (C.start q)
  floor-start q = subst (A.LeFam n (E.idx n q) (E.Ω (E.num n q))) (sym (ref-start q))
    (B.rfl n (E.idx n q) (proj₁ (B.Ω-model n (E.idx n q))))

record Change (n m : ℕ) {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) : Set where
  module S = A.Layer n (A.GoFam n) (A.LeFam n)
  module T = A.Layer m (A.GoFam m) (A.LeFam m)
  field
    pull : L.U i (L.<→◃ q) → L.U i (L.<→◃ p)
    good : ∀ u → T.GU q u → S.GU p (pull u)
    floor : ∀ u → T.Floor q u → S.Floor p (pull u)
    rel : ∀ u v → T.RU q u v → S.RU p (pull u) (pull v)
    start : pull (C.start q) ≡ C.start p
    next : ∀ u → pull (C.next q u) ≡ C.next p (pull u)

change : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) → Change n m p q
Change.pull (change n m p q) u = L.coe (L.<→◃ q) (L.<→◃ p) u
Change.good (change n m p q) u gu = subst (λ X → X) (sym (E.GU-eq n m p q u)) gu
Change.floor (change n m p q) u o = subst (λ X → X) (sym (E.floor-eq n m p q u)) o
Change.rel (change n m p q) u v r = subst (λ X → X) (sym (E.RU-eq n m p q u v)) r
Change.start (change n m p q) = C.coe-start q p
Change.next (change n m p q) u = C.coe-next q p u

actual₀ : Change 0 1 (L.zero {a = L.zero}) (L.suc L.zero)
actual₀ = change 0 1 L.zero (L.suc L.zero)
actual₁ : Change 1 2 (L.zero {a = L.suc L.zero}) (L.suc L.zero)
actual₁ = change 1 2 L.zero (L.suc L.zero)
```
