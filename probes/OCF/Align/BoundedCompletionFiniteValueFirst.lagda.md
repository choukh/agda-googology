# 全有限最高反馈的实际地板覆盖

将SelfKeep实际实例接入原coordinate与chain，交付全n值定理。
不把纯seed1当作地板；地板从真实前缀经第一次反馈进入坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueFirst where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans; ≤⊞)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueIf
open import OCF.Align.BoundedCompletionFiniteValueRebuild using (instance-self)
import OCF.Align.BoundedCompletionFiniteValueCompute as Compute
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ

module Actual = Compute.From instance-self

instance-first : FirstFloor
instance-first = Actual.instance-first
first-floor : ∀ n → floor n ≤ᵛ first n
first-floor = Actual.first-floor

emit : ∀ n → HB (Native (num n)) → HB (Native hz)
emit n c = at (suc n) zero {B = num (suc n)} (legal-num (suc n)) hself
  (z⊲ᴮ (num (suc n))) (up (Θ.model n) ⊞ up c)

normal-shape : ∀ n → Θ.normal (suc n) ≡ diagonal (coordinate n) (emit n)
normal-shape zero = refl
normal-shape (suc n) = refl

first-in-tail : ∀ n k → first n ≤ᵛ chain (coordinate n) (suc k)
first-in-tail n zero = OCF.Lean.Fold1Base.≤-refl _
first-in-tail n (suc k) = ≤-trans (first-in-tail n k) (≤⊞ _ _)

floor-in-tail : ∀ n k → floor n ≤ᵛ chain (coordinate n) (suc k)
floor-in-tail n k = ≤-trans (first-floor n) (first-in-tail n k)
```

normal-shape逐构造核对这些链正是原normal(suc n)使用的最高反馈，
不是新定义的替代轨道。floor-in-tail覆盖全部有限层及所有后续反馈项。

此值关系仍不能直接喂给任意Ω分支的折叠单调性；Old的世界更新和
地板初界还需要有向分支关系连接。尚未证明Old.TΩ有限族≤normalized，
因此本篇不报告新的ψ₀(Ω_x)下界，更不宣称EBO验收完成。
