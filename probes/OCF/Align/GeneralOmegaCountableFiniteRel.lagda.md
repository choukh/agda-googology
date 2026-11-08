# 两份真实有限塔之间的遗传坐标关系

研究验收工具。直接比较Countable.F(num n)与Finite.F n，避免把
KS类型等式当成任意g可消费Same。顶层坐标关系递归到下一低层，
实际floor、up、加法和全部迭代给出非空实例与闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaCountableObserveIf as C
import OCF.Lean.GeneralOmegaFiniteObserveIf as F
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)

data Kind : ∀ n → K (C.F (num n)) → K (F.F n) → Set where
  low : ∀ {n κ κ′} → Kind n κ κ′ → Kind (suc n) (inj₁ κ) (inj₁ κ′)
  high : ∀ {n} → Kind (suc n) (inj₂ tt) (inj₂ tt)

data Trees (n : ℕ)
  (Q : ∀ {κ κ′} → Kind n κ κ′ → E (C.F (num n)) κ → E (F.F n) κ′ → Set) :
  HB (C.F (num n)) → HB (F.F n) → Set where
  rz : Trees n Q hz hz
  rs : ∀ {a b} → Trees n Q a b → Trees n Q (hs a) (hs b)
  rl : ∀ {f g} → (∀ i → Trees n Q (f i) (g i)) → Trees n Q (hl f) (hl g)
  ro : ∀ {κ κ′ f g} (k : Kind n κ κ′) →
    (∀ {a b} → Q k a b → Trees n Q (f a) (g b)) → Trees n Q (hΩ κ f) (hΩ κ′ g)

mutual
  Rel : ∀ n → HB (C.F (num n)) → HB (F.F n) → Set
  Rel n = Trees n (Coord n)
  Coord : ∀ n {κ κ′} → Kind n κ κ′ → E (C.F (num n)) κ → E (F.F n) κ′ → Set
  Coord (suc n) (low k) = Coord n k
  Coord (suc n) high = Rel n

up-rel : ∀ {n a b} → Rel n a b → Rel (suc n) (up a) (up b)
up-rel rz = rz
up-rel (rs p) = rs (up-rel p)
up-rel (rl p) = rl (λ n → up-rel (p n))
up-rel (ro k p) = ro (low k) (λ q → up-rel (p q))
floor-rel : ∀ n → Rel n (C.floor (num n)) (F.floor n)
floor-rel zero = rs rz
floor-rel (suc n) = ro high (λ q → up-rel q)

add-rel : ∀ {n a b c d} → Rel n a b → Rel n c d → Rel n (a ⊞ c) (b ⊞ d)
add-rel p rz = p
add-rel p (rs q) = rs (add-rel p q)
add-rel p (rl q) = rl (λ n → add-rel p (q n))
add-rel p (ro k q) = ro k (λ r → add-rel p (q r))
left-rel : ∀ {n a b} → Rel n a b → ∀ i → Rel n (C.leftMul a i) (F.leftMul b i)
left-rel p zero = rz
left-rel p (suc i) = add-rel p (left-rel p i)
iterate-rel : ∀ {n} {f : HB (C.F (num n)) → HB (C.F (num n))} {g : HB (F.F n) → HB (F.F n)} →
  (∀ {a b} → Rel n a b → Rel n (f a) (g b)) → ∀ {a b} → Rel n a b →
  ∀ i → Rel n (C.iterate f a i) (F.iterate g b i)
iterate-rel fg p zero = p
iterate-rel fg p (suc i) = fg (iterate-rel fg p i)

zero-same : ∀ {a b} → Rel zero a b → Same a b
zero-same rz = zz
zero-same (rs p) = ss (zero-same p)
zero-same (rl p) = ll (λ n → zero-same (p n))
zero-same (ro () p)
```

这里还未证明Countable.classify与Finite.view保持此关系，也没有
由关系定义本身推出全有限观察一致性。新增域明确排除了任意raw
分支同余的偷渡；所有原有限地板则已在域内。
