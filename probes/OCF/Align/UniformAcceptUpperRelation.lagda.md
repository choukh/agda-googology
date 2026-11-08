# 现有末段逻辑关系不能直接比较两个零规则

欲以 Level 的第一不可数目标折叠作上界，实际 act 的零规则为1，
参照零规则为最低 Ω 地板。现有 VRel 的Ω右规则要求全部坐标统一下界，
因此无法提供这一基础字段。然而原末段的值比较在每个种子上都成立。
这只定位关系过强之处，不否定上界或参照的可能性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformAcceptUpperRelation where
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.FrozenAbsorbSeed using (right-add)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure using (floor; floor-self; seed-mono)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedCompletionValueAcceptOld as Old

one : HB U
one = hs hz

no-one-zero : VRel one hz → ⊥
no-one-zero ()
no-zero-rule : VRel (Old.act hz) floor → ⊥
no-zero-rule (vor p) = no-one-zero (p hz)

actual-zero-value : ∀ b → T.fold b (Old.act hz) ≤ᵛ T.fold b floor
actual-zero-value b = ≤-trans
  (≤l 1 (right-add (hs hz) (T.fold (hs hz) (up (hs hz)))))
  (seed-mono floor-self z≤)
```

比较前提均有真实对象：左侧就是原 act hz，右侧为原最低地板；种子b
任意，不是假设非法世界。故继续该上界比较需要接受这个已成立的
采样相关基础值比较的更细关系，不能直接要求 VRel 的原字段。
