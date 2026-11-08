# 真实第二样本中的动态双 Ω 下界

本篇选取原 normalized 1 的实际嵌套极限支；没有替换输入、坐标或运行器。
目标是完整动态双 Ω 输出，不是其有限数值截断。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionValueAcceptPair where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionTerminalValueIf
import OCF.Align.BoundedCompletionTerminalValueRun as VR
import OCF.Align.BoundedCompletionValueAcceptModel as M
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionFinitePlaceSample as Actual
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeCompletionClosed as C
open import OCF.Align.FrozenAbsorbNegUpper using (P; infl)
open import OCF.Lean.NegFold1If using (Sm; sz; ss; sl; Sm-⊞)

small : HB U
small = M.low (up (up (Θ.model zero)))

pure-low : ∀ {a c} → Sm a c → Sm (M.low a) (P (hs hz) c)
pure-low sz = ss sz
pure-low (ss p) = sl (V.partial-pure (pure-low p))
pure-low (sl p) = sl (λ n → pure-low (p n))

source-pure : ∀ (c : Cd) → Sm (up (up (hz ⊞ up c))) c
source-pure hz = sz
source-pure (hs c) = ss (source-pure c)
source-pure (hl f) = sl (λ n → source-pure (f n))

pure-target : ∀ {h : HB U} {a b : Cd} → Sm h b → a ≤ᵛ b → VRel (up a) h
pure-target p z≤ = vz
pure-target (ss p) (s≤s q) = vs (pure-target p q)
pure-target (ss p) (≤s q) = vr (pure-target p q)
pure-target p (l≤ q) = vl (λ n → pure-target p (q n))
pure-target (sl p) (≤l n q) = vli n (pure-target (p n) q)

floor≤small : VRel (floor zero) small
floor≤small = vo (λ {c} {d} cd → pure-target (pure-low (source-pure d))
  (≤-trans cd (infl (hs hz) (≤-refl (hs hz)) d)))

selected≤output : T.fold V.feedback (small ⊞ small) ≤ᵛ M.output
selected≤output = ≤l 0 (≤l 0 (≤l 0 (≤l 1 (≤-refl _))))
```

```agda
open import OCF.Align.BoundedCompletionTerminalValueClosure using (add-rel)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)

pair : HB U
pair = floor zero ⊞ floor zero
pair-output : Cd
pair-output = T.fold hz pair

pair≤normalized : pair-output ≤ᵛ Actual.normalized 1
pair≤normalized = ≤-trans
  (VR.eval (add-rel floor≤small floor≤small) z≤)
  (≤-trans selected≤output (same-value (same-sym M.actual-output)))
pair≤C : pair-output ≤ᵛ C.tree
pair≤C = ≤-trans pair≤normalized (Actual.normalized-below-C 1)
```

双 Ω 使用原末段的动态回灌，包含全部内轨道。此下界已接原合法完成项 C；
尚未由此证明 C 覆盖 Old.TΩ2 或带标签的 ψ₀(Ω₂)。
