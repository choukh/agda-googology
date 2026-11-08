# 外层分量位置捕获的完整观察值

树侧接口只读取每个原分量到实际目标分量的字面位置。此篇在验收层
利用已完成typed观察桥证明值包含；不把Sim当旧层前驱包含，不穿leg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableOuterCaptureRun where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableOuterCaptureIf
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.LambdaCountableBridge as Z
import OCF.Align.LambdaOrderBridge as Order
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-position)
open import OCF.Align.GeneralOmegaCountableTypedValueReference using (reference-shape)

layer-capture : ∀ (f g : ℕ → Cd) (lf : LgB (hl f)) (lg : LgB (hl g)) →
  (∀ n → Σ ℕ (λ m → f n ⊲ g m)) → height (hl f) lf L.⊑ᴵ height (hl g) lg
layer-capture f g lf lg access = L.l⊑ branch
  where
  branch : ∀ n → height (f n) (proj₂ lf n) L.⊑ᴵ height (hl g) lg
  branch n with access n
  ... | m , p = height-position (proj₂ lf n) lg (hlim m p)

capture : ∀ (f g : ℕ → Cd) (lf : LgB (hl f)) (lg : LgB (hl g)) →
  (∀ n → Σ ℕ (λ m → f n ⊲ g m)) → point-root (hl f) lf ≤ᵛ point-root (hl g) lg
capture f g lf lg access = ≤-trans
  (same-value (same-sym (reference-shape (hl f) lf (z⊲ᴮ (hl f)))))
  (≤-trans
    (Z.forget-mono (Order.backward (V.⊑→≼ _ (L.Ψ⁰-mono (layer-capture f g lf lg access)))))
    (same-value (reference-shape (hl g) lg (z⊲ᴮ (hl g)))))

instance-capture : OuterPositionCapture
instance-capture = record { capture = capture }
```

capture覆盖整输出，不是有限抽样。每次height-position的共同上界
为原目标hl g，路径先入第m分量再用给定p。未推出后继内部加速，
未推出Γ值单调，亦未把原观察器换成逐点地板定义。
