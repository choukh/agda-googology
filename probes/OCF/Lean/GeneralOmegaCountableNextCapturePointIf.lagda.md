# 逐点地板反馈的辅助解释器接口

研究参照：零叶和每个反馈种子均改用pointFloor，其规则受旧typed
参照启发。种类、分类、真实路径及source递归不变；这不是新成品。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableNextCapturePointIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf using (Sim)

point-node : ∀ {B t A} → t ⊲ B → C.Dc F B t A →
  (∀ r → r ⊲ B → A → HB (F r)) → HB (F t)
point-node {t = t} pt (C.keep κ fr) rec = hΩ κ (λ e → rec t pt (fr e))
point-node {t = t} pt (C.same to) rec = hl (λ n → rec t pt
  (to (iterate (λ e → rec t pt (to e)) (pointFloor t) n)))
point-node {t = t} pt (C.above r pr tr to) rec = hl (λ n → rec t pt
  (to (iterate (λ e → rec r (⊲ᴮ-tr (hsuc hself) pr) (to e)) (pointFloor r) n)))

point-observe : ∀ B → LgB B → ∀ t → t ⊲ B → HB (F B) → HB (F t)
point-observe B lB t pt hz = pointFloor t
point-observe B lB t pt (hs a) = hl (leftMul (point-observe B lB t pt a))
point-observe B lB t pt (hl f) = hl (λ n → point-observe B lB t pt (f n))
point-observe B lB t pt (hΩ κ f) = point-node pt (classify B lB t pt κ)
  (λ r pr e → point-observe B lB r pr (f e))

record PointSimulation : Set₁ where
  field
    simulate : ∀ B lB t pt {a b} → Sim B a b →
      Sim t (point-observe B lB t pt a) (observe B lB t pt b)
```

待填字段比较两个原source子树上的完整解释，不以输入floor界充当
反馈界；非空实例在实现中取所有B的原floor及pointFloor。
