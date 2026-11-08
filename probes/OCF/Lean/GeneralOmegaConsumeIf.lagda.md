# 不保留Ω节点的全层可数解释接口

独立检验全部Ω直接回灌到Cd这一算法选择。既然没有keep，原源分支
函数已接受其坐标类型的全部对象，不必先把整个raw坐标域补成Supported。
每种坐标依其真实低层类型编码，输入可以取完整ΛL地板。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaConsumeIf where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.HigherIndexConsumeCode using (from; pure)
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)

code : ∀ x κ → Cd → E (Lv x) κ
code x κ d = from x κ (flL (lvl x κ) ⊞ pure (Lv (lvl x κ)) (leg d))

record Consumer : Set₁ where
  field
    run : ∀ x → HB (Lv x) → Cd
    zero : ∀ x → run x hz ≡ hs hz
    successor : ∀ x a → run x (hs a) ≡ Ops.repeat S⊥ (run x a)
    limit : ∀ x f → run x (hl f) ≡ hl (λ n → run x (f n))
    omega : ∀ x κ f → run x (hΩ κ f) ≡
      diagonal (λ d → run x (f (code x κ d))) (λ d → run x (f (code x κ d)))
```

code无下标判等或全局比较；只由种类的坐标类型读出低层。地板加纯树
是实验选择，未证明其树侧唯一性或旧折叠保值。接口的逐构造子方程
防止用任意常值run充当实例。合法性与值均对实际实现另行验收。
