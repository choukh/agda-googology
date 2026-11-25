# YiXVCountableChain
> 验收文件。档位：编译定理。带地板的链及两链的逐项、输出极限比较。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableChainInput as Q

module Chain {κ} (P : L.Ordᶜ κ → L.Ordᶜ κ) (input : Q.Input P) where
  d : ℕ → L.Ordᶜ κ
  d = iter P (L.Ω κ)
  mutual
    good : ∀ n → A.Gd (d n)
    good zero = proj₁ (O.model κ)
    good (suc n) = Q.Input.good input (d n) (good n) (floor n)
    floor : ∀ n → A.Le (L.Ω κ) (d n)
    floor zero = A.Layer.rfl κ A.Gd< A.Le< (proj₁ (O.model κ))
    floor (suc n) = Q.Input.floor input (d n) (good n) (floor n)

module Compare {κ} (P R : L.Ordᶜ κ → L.Ordᶜ κ) (p : Q.Input P) (r : Q.Input R)
  (h : ∀ X Y → A.Gd X → A.Gd Y → A.Le (L.Ω κ) X → A.Le X Y → A.Le (P X) (R Y)) where
  module C = Chain P p
  module D = Chain R r
  bound : ∀ n → A.Le (C.d n) (D.d n)
  bound zero = A.Layer.rfl κ A.Gd< A.Le< (proj₁ (O.model κ))
  bound (suc n) = h (C.d n) (D.d n) (C.good n) (D.good n) (C.floor n) (bound n)
  module Lim {ν} (F G : L.Ordᶜ κ → L.Ordᶜ ν)
    (gf : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Gd (F X))
    (gg : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Gd (G X))
    (m : ∀ X Y → A.Gd X → A.Gd Y → A.Le (L.Ω κ) X → A.Le X Y → A.Le (F X) (G Y)) where
    left right : ℕ → L.Ordᶜ ν
    left n = F (C.d n)
    right n = G (D.d n)
    result : A.Le (L.lim left) (L.lim right)
    result = A.Layer.pack (A.Layer.gl (λ n → gf (C.d n) (C.good n) (C.floor n)))
      (A.Layer.gl (λ n → gg (D.d n) (D.good n) (D.floor n)))
      (A.Layer.ll (λ n → A.Layer.pack (gf (C.d n) (C.good n) (C.floor n))
        (A.Layer.gl (λ k → gg (D.d k) (D.good k) (D.floor k)))
        (A.Layer.lr n (m (C.d n) (D.d n) (C.good n) (D.good n) (C.floor n) (bound n)))))

module Model (κ : L.Ordᴵ) where
  module C = Compare (λ X → L.Ω κ) (λ X → L.Ω κ) (Q.model κ) (Q.model κ)
    (λ X Y gx gy o t → A.Layer.rfl κ A.Gd< A.Le< (proj₁ (O.model κ)))
  actual : ∀ n → A.Le (C.C.d n) (C.D.d n)
  actual = C.bound
```
