# 三步延迟覆盖旧坐标与补偿部分和

每个旧步骤使用三个真实新反馈步骤：先覆盖旧下一坐标，再并入累计输入，
最后用统一的1下界吸收输出加法所需的后继。没有假定hsΩ≤actΩ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputCoverStride where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure using (prefix-rel; add-rel; floor-self)
open import OCF.Align.BoundedCompletionTerminalValueAct using (act-mono; inflate; positive)
open import OCF.Align.BoundedCompletionOutputPadding using (right-rel; pad)
import OCF.Align.BoundedCompletionValueAcceptOld as Old
open import OCF.Align.BoundedCompletionOutputCoverModel using (prefix; H)

step-inflate : ∀ {a b} → VRel a b → VRel a (H b)
step-inflate p = inflate (right-rel prefix p)
step-act : ∀ {a b} → VRel a b → VRel (Old.act a) (H b)
step-act p = act-mono (right-rel prefix p)
step-positive : ∀ b → VRel (hs hz) (H b)
step-positive b = positive (prefix ⊞ b)

stride : ℕ → ℕ
stride zero = 1
stride (suc n) = suc (suc (suc (stride n)))

initial : VRel (Old.Pure.ce zero) (chain H 1)
initial = right-rel (hs hz)
  (inflate (prefix-rel (right-rel hz floor-self) (hs hz)))

coordinates : ∀ n → VRel (Old.Pure.ce n) (chain H (stride n))
padded : ∀ n → VRel (pad Old.Pure.ce n) (chain H (stride n))
coordinates zero = initial
coordinates (suc n) =
  prefix-rel
    (prefix-rel (add-rel (coordinates n) (step-act (coordinates n)))
      (H (chain H (suc (stride n)))))
    (H (chain H (suc (suc (stride n)))))
padded zero = initial
padded (suc n) = add-rel
  (add-rel
    (prefix-rel (padded n) (H (chain H (stride n))))
    (step-inflate (add-rel (coordinates n) (step-act (coordinates n)))))
  (step-positive (chain H (suc (suc (stride n)))))

last-rel : ∀ n {a} → VRel a (H (chain H n)) →
  VRel a (Ops.partial U (λ k → H (chain H k)) n)
last-rel zero p = p
last-rel (suc n) p = right-rel _ p

padded-partial : ∀ n → VRel (pad Old.Pure.ce n)
  (Ops.partial U (λ k → H (chain H k)) (stride n))
padded-partial n = last-rel (stride n) (step-inflate (padded n))
```

padded-partial是所需的整输出输入覆盖，右边是完整原模型输出的真实部分和，
不是只比较某一个旧坐标，也没有替换任何旧/新轨道。
