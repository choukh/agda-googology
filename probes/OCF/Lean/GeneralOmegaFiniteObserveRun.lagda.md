# 全有限塔的结构递归观察器

所有递归调用只落在当前源树的直接子树。反馈层与输出层共用同一
原分支f；反馈所得完整低层HB重新作为f的坐标，无累加或纯尾编码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteObserveRun where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf

observe : ∀ {n m} → Within n m → HB (F n) → HB (F m)
observe {m = m} p hz = floor m
observe p (hs a) = hl (leftMul (observe p a))
observe p (hl f) = hl (λ i → observe p (f i))
observe p (hΩ κ f) = node p (view p κ) (λ k q e → observe q (f e))

instance-observer : Observer
instance-observer = record
  { observe = observe
  ; at-zero = λ p → refl
  ; at-successor = λ p a → refl
  ; at-limit = λ p f → refl
  ; at-node = λ p κ f → refl }
```

相等目标的here不是恒等函数：它是以目标floor为零点、保留全部旧Ω
的typed动作。实际坍缩只通过lower路径发生；本篇未宣称一般raw合法
输入的输出合法或原Level值桥已经完成。
