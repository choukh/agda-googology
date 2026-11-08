# 有限层统一下降到P

迭代本轮已证明的一步down。它是独立构造，不声称与原M的跨多层
直接fold相同；OriginalPointwise仍是另一个尚未完成的验收目标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegDescent where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegFold

collapse : ∀ n → HB (F n) → HB (F zero)
collapse zero a = a
collapse (suc n) a = collapse n (down n a)

collapse-good : ∀ n a → Good n a → Good zero (collapse n a)
collapse-good zero a p = p
collapse-good (suc n) a p = collapse-good n (down n a) (down-good n a p)

collapse-legal : ∀ n a → Good n a → LgB (collapse n a)
collapse-legal n a p = proj₂ (collapse-good n a p)

family-sum : (∀ n → HB (F n)) → HB (F zero)
family-sum f = Ops.sum (F zero) (λ n → collapse n (f n))
family-legal : ∀ f → (∀ n → Good n (f n)) → LgB (family-sum f)
family-legal f p = LegalSum.sum-legal (F zero) _ (λ n → collapse-legal n (f n) (p n))
```

P仍是高层种类结构，不是可数终点。接口前提的实际全有限地板实例
由本轮Up模块提供；本篇不以常值零族代替它，也不声称已有ψ₀Λ值定理。
