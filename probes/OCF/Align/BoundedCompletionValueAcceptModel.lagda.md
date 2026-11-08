# 真实第二样本的三个种类解释

验收模型仅消去有限分类计算。右侧保持原 seed=1、坐标累加和输出累加，
并非旧 Fold1 的世界更新模型。必须由下文实际结构桥才用于原 normalized 1。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionValueAcceptModel where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedDescentValueBridge using (Native)
import OCF.Lean.BoundedDiagonalRel as D

low : HB (Native (num 2)) → HB (Native hz)
mid : HB (Native (num 2)) → HB (Native (num 1))
low hz = hs hz
low (hs a) = Ops.repeat _ (low a)
low (hl f) = hl (λ n → low (f n))
low (hΩ (inj₁ (inj₁ (inj₁ ()))) g)
low (hΩ (inj₁ (inj₁ (inj₂ _))) g) = hΩ (inj₂ tt) (λ e → low (g e))
low (hΩ (inj₁ (inj₂ _)) g) = diagonal (λ e → low (g e)) (λ e → low (g e))
low (hΩ (inj₂ _) g) = diagonal (λ e → mid (g e)) (λ e → low (g e))
mid hz = hs hz
mid (hs a) = Ops.repeat _ (mid a)
mid (hl f) = hl (λ n → mid (f n))
mid (hΩ (inj₁ (inj₁ (inj₁ ()))) g)
mid (hΩ (inj₁ (inj₁ (inj₂ _))) g) = hΩ (inj₁ (inj₂ tt)) (λ e → mid (g e))
mid (hΩ (inj₁ (inj₂ _)) g) = hΩ (inj₂ tt) (λ e → mid (g e))
mid (hΩ (inj₂ _) g) = diagonal (λ e → mid (g e)) (λ e → mid (g e))

low-rel : ∀ {a b} → Rel (num 2) a b →
  Rel hz (at 2 zero tt hself (hsuc (hsuc hself)) a) (low b)
mid-rel : ∀ {a b} → Rel (num 2) a b →
  Rel (num 1) (at 2 1 tt hself (hsuc hself) a) (mid b)
low-rel rz = rs rz
low-rel (rs p) = rel-repeat (low-rel p)
low-rel (rl p) = rl (λ n → low-rel (p n))
low-rel (ro {κ = inj₁ (inj₁ (inj₁ ()))} p)
low-rel (ro {κ = inj₁ (inj₁ (inj₂ _))} p) = ro (λ x y r → low-rel (p x y r))
low-rel (ro {κ = inj₁ (inj₂ _)} {f} {g} p) = D.Sim.result
  (Rel hz) (Rel hz)
  (λ e → at 2 zero tt hself (hsuc (hsuc hself)) (f e)) (λ e → low (g e))
  (λ e → at 2 zero tt hself (hsuc (hsuc hself)) (f e)) (λ e → low (g e))
  (rs rz) rel-add rel-add rl
  (λ r → low-rel (p _ _ r)) (λ r → low-rel (p _ _ r))
low-rel (ro {κ = inj₂ _} {f} {g} p) = D.Sim.result
  (Rel (num 1)) (Rel hz)
  (λ e → at 2 1 tt hself (hsuc hself) (f e)) (λ e → mid (g e))
  (λ e → at 2 zero tt hself (hsuc (hsuc hself)) (f e)) (λ e → low (g e))
  (rs rz) rel-add rel-add rl
  (λ r → mid-rel (p _ _ r)) (λ r → low-rel (p _ _ r))
mid-rel rz = rs rz
mid-rel (rs p) = rel-repeat (mid-rel p)
mid-rel (rl p) = rl (λ n → mid-rel (p n))
mid-rel (ro {κ = inj₁ (inj₁ (inj₁ ()))} p)
mid-rel (ro {κ = inj₁ (inj₁ (inj₂ _))} p) = ro (λ x y r → mid-rel (p x y r))
mid-rel (ro {κ = inj₁ (inj₂ _)} p) = ro (λ x y r → mid-rel (p x y r))
mid-rel (ro {κ = inj₂ _} {f} {g} p) = D.Sim.result
  (Rel (num 1)) (Rel (num 1))
  (λ e → at 2 1 tt hself (hsuc hself) (f e)) (λ e → mid (g e))
  (λ e → at 2 1 tt hself (hsuc hself) (f e)) (λ e → mid (g e))
  (rs rz) rel-add rel-add rl
  (λ r → mid-rel (p _ _ r)) (λ r → mid-rel (p _ _ r))

import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionFinitePlaceSample as Actual
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeCompletionClosed as C
open import OCF.Align.BoundedCompletionTerminalRel using (terminal-rel)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)

actual-input : Rel hz (Θ.normal 2) (low (Θ.model 2))
actual-input = low-rel (Θ.model-rel 2)

output : Cd
output = T.fold V.feedback (low (Θ.model 2))
actual-output : Same (Actual.normalized 1) output
actual-output = terminal-rel actual-input (pure-reflexive V.feedback)
output≤C : output ≤ᵛ C.tree
output≤C = ≤-trans (same-value (same-sym actual-output)) (Actual.normalized-below-C 1)
```

这里的实例覆盖实际 model 2 的所有反馈分支，不是有限展开测试；
但模型与 Old.TΩ2 的比较仍需独立轨道定理，不能用种类数命名值。
