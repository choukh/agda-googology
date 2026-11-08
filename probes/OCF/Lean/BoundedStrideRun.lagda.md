# 全树关系的统一三步覆盖

不按层重写归纳。一次旧步骤被三个原chain H步骤覆盖，最后一个H
输出提供后继补偿；再直接进入原输出部分和。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedStrideRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.BoundedStrideIf

stride : ℕ → ℕ
stride zero = 1
stride (suc n) = suc (suc (suc (stride n)))

module Run {S R F H old padded} (laws : StrideLaws S R F H old padded) where
  open StrideLaws laws

  coordinates : ∀ n → R (old n) (chain H (stride n))
  coordinates zero = initial
  coordinates (suc n) rewrite old-step n =
    append
      (append (add (coordinates n) (action (coordinates n)))
        (H (chain H (suc (stride n)))))
      (H (chain H (suc (suc (stride n)))))

  padded-coordinates : ∀ n → R (padded n) (chain H (stride n))
  padded-coordinates zero rewrite pad-zero = initial
  padded-coordinates (suc n) rewrite pad-step n | old-step n = add
    (add
      (append (padded-coordinates n) (H (chain H (stride n))))
      (inflate (add (coordinates n) (action (coordinates n)))))
    (positive (chain H (suc (suc (stride n)))))

  last-rel : ∀ n {a} → R a (H (chain H n)) →
    R a (Ops.partial S (λ k → H (chain H k)) n)
  last-rel zero p = p
  last-rel (suc n) p = prepend _ p

  padded-partial : ∀ n → R (padded n)
    (Ops.partial S (λ k → H (chain H k)) (stride n))
  padded-partial n = last-rel (stride n) (inflate (padded-coordinates n))
```

全部字段的实际满足性由独立实例文件给出；本篇不把抽象实例存在
当作已提高强度。它没有增加树节点、种类或新的回灌运行器。
