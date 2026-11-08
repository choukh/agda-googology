# 有限原下标的字面秩分解

验收辅助。公共界是原类型nat n；其下每个原下标不仅模某个关系
等于有限数，而是字面等于nat k。分解直接递归公共有限界及其路径，
不对一般Ordᴵ作判定，也不要求任何不可数共尾元位于有限界内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteRank where
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.GeneralOmegaFiniteObserveIf as I

nat : ℕ → L.Ordᴵ
nat zero = L.zero
nat (suc n) = L.suc (nat n)

record Rank {n : ℕ} {a : L.Ordᴵ} (p : a L.<ᴵ nat n) : Set where
  constructor rank
  field
    number : ℕ
    bounded : number < n
    literal : a ≡ nat number
open Rank public

decompose : ∀ {n a} (p : a L.<ᴵ nat n) → Rank {n = n} p
decompose {n = zero} ()
decompose {n = suc n} L.zero = rank n (Data.Nat.s≤s ≤-refl) refl
decompose {n = suc n} (L.suc p) with decompose {n = n} p
... | rank k b e = rank k (≤-step b) e

ambient : ∀ {n m} → I.Within n m → nat m L.<ᴵ nat (suc n)
ambient I.here = L.zero
ambient (I.lower p) = L.suc (ambient p)

-- 实际最高种类的原下标和反馈层确实就是有限数n。
top : ∀ n → Rank {n = suc n} (L.zero {a = nat n})
top n = decompose {n = suc n} L.zero
```

这提供有限观察器验收需要的类型等式；没有声称已比较整个观察值。
其中top对所有n给非空实例。共同有限源界仍须保留在跨up的观察律里，
不能在读回较低层对象后丢掉ambient参数。
