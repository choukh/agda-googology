# YiXVReadOmegaLimit
> 验收文件。档位：编译定理。逐支模拟以原部分和形状组成自然极限模拟，含实际 ω 完整闭实例。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadOmegaLimit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadOmegaInput as Q
module Limit (f : ℕ → S.Tr S.zero) (a : ∀ n → S.zero S.⊢ f n ◃ f (suc n))
  (C : ∀ n → L.Ordᶜ (T.lvl (f n))) (input : Q.Branches f C) where
  x = S.lim f a
  κ = T.lvl x
  module D = A.Layer κ A.Gd< A.Le<
  module R = U.Layer x (U.Fam x)
  partial : ℕ → L.Ordᶜ κ
  partial zero = L.add (L.Ω κ) (J.σchild x zero) (C zero)
  partial (suc n) = L.add (partial n) (J.σchild x (suc n)) (C (suc n))
  good-partial : ∀ n → A.Gd (partial n)
  good-partial zero = Add.good (proj₁ (Ω.model κ)) (Q.Branches.good input zero)
  good-partial (suc n) = Add.good (good-partial n) (Q.Branches.good input (suc n))
  cover-partial : ∀ n → U.UR x (O.cumΩ (λ k → J.ℓ (f k)) n) (partial n)
  cover-partial zero = R.uu zero (proj₁ (Ω.model κ)) R.uz
    (Q.Branches.good input zero) (Q.Branches.cover input zero)
  cover-partial (suc n) = R.uu (suc n) (good-partial n) (cover-partial n)
    (Q.Branches.good input (suc n)) (Q.Branches.cover input (suc n))
  cap : L.Ordᶜ κ
  cap = L.lim partial
  good : A.Gd cap
  good = D.gl good-partial
  cover : U.UR x (O.Ωt (J.ℓ x)) cap
  cover = R.ul (λ n → R.uw (cover-partial n)
    (D.pack (good-partial n) good (D.lr n (D.rfl (good-partial n)))))

module Model = Limit Q.nat (λ n → S.◃s) Q.cap Q.model
actual : U.UR Q.ω (O.Ωt (J.ℓ Q.ω)) Model.cap
actual = Model.cover
```
