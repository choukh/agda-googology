# YiXVReadOmega
> 验收文件。档位：编译定理。沿实际源层号递归构造参照闭树及其合法性、Ω 源模拟证书；未给参照闭树的值界。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadOmega where
open import Data.Product using (proj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadOmegaInput as Q
import OCF.Lean.YiXVReadOmegaLimit as Lim
mutual
  cap : ∀ x → L.Ordᶜ (T.lvl x)
  cap S.zero = L.Ω L.zero
  cap (S.suc x) = L.Ω (T.lvl (S.suc x)) L.+ L.Ω (T.lvl (S.suc x))
  cap (S.lim f a) = Lim.Limit.cap f a (λ n → cap (f n)) (branches f)
  cap (S.Ω () g)
  cap (S.up x () y e)
  good : ∀ x → A.Gd (cap x)
  good S.zero = proj₁ (Ω.model L.zero)
  good (S.suc x) = Add.good {σ = λ q → q} (proj₁ (Ω.model (T.lvl (S.suc x))))
    (proj₁ (Ω.model (T.lvl (S.suc x))))
  good (S.lim f a) = Lim.Limit.good f a (λ n → cap (f n)) (branches f)
  good (S.Ω () g)
  good (S.up x () y e)
  cover : ∀ x → U.UR x (O.Ωt (J.ℓ x)) (cap x)
  cover S.zero = ≼-refl _
  cover (S.suc x) = B.Ωsuc x
  cover (S.lim f a) = Lim.Limit.cover f a (λ n → cap (f n)) (branches f)
  cover (S.Ω () g)
  cover (S.up x () y e)
  branches : ∀ f → Q.Branches f (λ n → cap (f n))
  Q.Branches.good (branches f) n = good (f n)
  Q.Branches.cover (branches f) n = cover (f n)
actual : U.UR Q.ω (O.Ωt (J.ℓ Q.ω)) (cap Q.ω)
actual = cover Q.ω
```
