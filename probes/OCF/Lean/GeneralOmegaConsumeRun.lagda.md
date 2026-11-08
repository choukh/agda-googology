# 对任意LH源树的同一个总解释器

递归只落在原源树的直接子树。x不作逐阶段展开，所有Ω共享同一Cd
回灌，坐标编码本身不调用run；停机直接交给Agda检查。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaConsumeRun where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.GeneralOmegaConsumeIf
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)

run : ∀ x → HB (Lv x) → Cd
run x hz = hs hz
run x (hs a) = Ops.repeat S⊥ (run x a)
run x (hl f) = hl (λ n → run x (f n))
run x (hΩ κ f) = diagonal branch branch
  where
  branch : Cd → Cd
  branch d = run x (f (code x κ d))

instance-consumer : Consumer
instance-consumer = record
  { run = run
  ; zero = λ _ → refl
  ; successor = λ _ _ → refl
  ; limit = λ _ _ → refl
  ; omega = λ _ _ _ → refl }
```

这个全层算法不依赖之前的世界准入证书；这并不使之前证书或旧算法
失效。改变的是算法的输出策略，是否达到目标值须直接证明。
