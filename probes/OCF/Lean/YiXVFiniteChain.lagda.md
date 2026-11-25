# YiXVFiniteChain
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteFloor as Floor

module Chain (m : ℕ) {k a : L.Ordᴵ} (p : L.natᴵ m L.<ᴵ a) (σ : L.Simᴵ k a) (f : I.T m → L.Ordᶜ k)
  (b : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd m (L.ψ p σ (f x))) where
  P : I.T m → I.T m
  P x = L.ψ p σ (f x)
  d : ℕ → I.T m
  d = iter P (L.Ω (L.natᴵ m))
  mutual
    good : ∀ n → A.Gd m (d n)
    good zero = proj₁ (B.Ω-model m F.zero)
    good (suc n) = b (d n) (good n) (floor n)
    floor : ∀ n → A.Le m (L.Ω (L.natᴵ m)) (d n)
    floor zero = B.rfl m F.zero {X = L.Ω (L.natᴵ m)} (proj₁ (B.Ω-model m F.zero))
    floor (suc n) = Floor.floor m p σ (f (d n)) (good (suc n))

module Compare (m : ℕ) {k a c : L.Ordᴵ} (p : L.natᴵ m L.<ᴵ a) (q : L.natᴵ m L.<ᴵ c)
  (σ : L.Simᴵ k a) (τ : L.Simᴵ k c) (f g : I.T m → L.Ordᶜ k)
  (bf : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd m (L.ψ p σ (f x)))
  (bg : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd m (L.ψ q τ (g x)))
  (h : ∀ x y → A.Gd m x → A.Gd m y → A.Le m (L.Ω (L.natᴵ m)) x → A.Le m x y →
    A.Le m (L.ψ p σ (f x)) (L.ψ q τ (g y))) where
  module C = Chain m p σ f bf
  module D = Chain m q τ g bg
  bound : ∀ n → A.Le m (C.d n) (D.d n)
  bound zero = B.rfl m F.zero {X = L.Ω (L.natᴵ m)} (proj₁ (B.Ω-model m F.zero))
  bound (suc n) = h (C.d n) (D.d n) (C.good n) (D.good n) (C.floor n) (bound n)

  module Lim (j : ℕ) (F G : I.T m → I.T j)
    (gF : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd j (F x))
    (gG : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd j (G x))
    (H : ∀ x y → A.Gd m x → A.Gd m y → A.Le m (L.Ω (L.natᴵ m)) x → A.Le m x y → A.Le j (F x) (G y)) where
    left right : ℕ → I.T j
    left n = F (C.d n)
    right n = G (D.d n)
    good-left : ∀ n → A.Gd j (left n)
    good-left n = gF (C.d n) (C.good n) (C.floor n)
    good-right : ∀ n → A.Gd j (right n)
    good-right n = gG (D.d n) (D.good n) (D.floor n)
    result : A.Le j (L.lim left) (L.lim right)
    result = B.ll j F.zero {a = left} {Y = L.lim right} good-left (B.gl j F.zero {a = right} good-right)
      (λ n → B.lr j F.zero {X = left n} {a = right} (good-left n) good-right n
        (H (C.d n) (D.d n) (C.good n) (D.good n) (C.floor n) (bound n)))

emptySim : ∀ a → L.Simᴵ L.zero a
emptySim a ()
module Model (m j : ℕ) where
  f : I.T m → I.T zero
  f x = L.zero
  gb : ∀ x → A.Gd m x → A.Le m (L.Ω (L.natᴵ m)) x → A.Gd m (L.ψ L.zero (emptySim (L.suc (L.natᴵ m))) (f x))
  gb x gx o = proj₁ (B.Ω-model m F.zero)
  cmp : ∀ x y → A.Gd m x → A.Gd m y → A.Le m (L.Ω (L.natᴵ m)) x → A.Le m x y →
    A.Le m (L.ψ L.zero (emptySim (L.suc (L.natᴵ m))) (f x)) (L.ψ L.zero (emptySim (L.suc (L.natᴵ m))) (f y))
  cmp x y gx gy o p = B.rfl m F.zero {X = L.Ω (L.natᴵ m)} (proj₁ (B.Ω-model m F.zero))
  module C = Compare m L.zero L.zero (emptySim (L.suc (L.natᴵ m))) (emptySim (L.suc (L.natᴵ m))) f f gb gb cmp
  out : I.T m → I.T j
  out x = L.Ω (L.natᴵ j)
  module D = C.Lim j out out (λ x gx o → proj₁ (B.Ω-model j F.zero)) (λ x gx o → proj₁ (B.Ω-model j F.zero))
    (λ x y gx gy o p → B.rfl j F.zero {X = L.Ω (L.natᴵ j)} (proj₁ (B.Ω-model j F.zero)))
  actual = D.result
```
