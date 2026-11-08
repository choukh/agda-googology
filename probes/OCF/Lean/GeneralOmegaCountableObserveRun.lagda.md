# 同一合法可数公共界内的总直接观察

源高度与其合法证据在递归中保持；变化的只是目标及它在原界内的
实际路径。每次递归都处理当前源节点的直接子树，因此不需要把
已折输出再次当作递归源，也不需要停机指示。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveRun where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf

observe : ∀ B → LgB B → ∀ t → t ⊲ B → HB (F B) → HB (F t)
observe B lB t pt hz = floor t
observe B lB t pt (hs a) = hl (leftMul (observe B lB t pt a))
observe B lB t pt (hl f) = hl (λ n → observe B lB t pt (f n))
observe B lB t pt (hΩ κ f) = node pt (classify B lB t pt κ)
  (λ r pr e → observe B lB r pr (f e))

instance-observer : Observer
instance-observer = record
  { observe = observe
  ; at-zero = λ B lB t pt → refl
  ; at-successor = λ B lB t pt a → refl
  ; at-limit = λ B lB t pt f → refl
  ; at-node = λ B lB t pt κ f → refl }
```

本篇只保证总定义与原接口四方程。一般输入的raw输出合法性、路径
无关性及值界都不在此结论内；最终可数完成闭项下一篇直接给出。
