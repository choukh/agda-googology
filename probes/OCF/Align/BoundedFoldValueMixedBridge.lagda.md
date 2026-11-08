# 全混合折叠中的真实旧 Ω 回灌分支

比较全自然数 Safe 混合的第1部分和与已有合法的旧 Ω 前缀回灌。
比较全部反馈坐标，不把输入替换成该单分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFoldValueMixedBridge where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
open import OCF.Align.FrozenOutputModel using (same-trans)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Lean.BoundedFoldClosed as C
import OCF.Align.BoundedFoldValueFeedback as V

fold : HB M.S → HB (T hz)
fold = M.Fold.fold hz (z⊲ᴮ _)

-- 第零分量的全部旧种类由分类器保留，坐标不变。
base-action : ∀ c → Same (fold (M.put 0 c)) (C.act c)
base-action hz = ss zz
base-action (hs c) = ll (same-repeat c)
  where
  same-repeat : ∀ c n → Same (Ops.partial (T hz) (λ _ → fold (M.put 0 c)) n)
    (Ops.partial (T hz) (λ _ → C.act c) n)
  same-repeat c zero = base-action c
  same-repeat c (suc n) = same-add (same-repeat c n) (base-action c)
base-action (hl f) = ll (λ n → base-action (f n))
base-action (hΩ κ g) = oo (λ e → base-action (g e))

repeat-same : ∀ {a b : HB (T hz)} → Same a b → ∀ n →
  Same (Ops.partial (T hz) (λ _ → a) n) (Ops.partial (T hz) (λ _ → b) n)
repeat-same p zero = p
repeat-same p (suc n) = same-add (repeat-same p n) p

-- 第1部分和的分支=旧前缀+新层up c；对任意结构相关的c,d同时比较。
next : HB (T hz) → HB (T hz)
next c = fold (M.floor 0 ⊞ M.put 1 (up c))
next-same : ∀ {c d} → Same c d → Same (next c) (C.next d)
next-same zz = base-action C.a
next-same (ss p) = ll (repeat-same (next-same p))
next-same (ll p) = ll (λ n → next-same (p n))
next-same (oo p) = oo (λ c → next-same (p c))

coordinates : ∀ n → Same (chain next n) (chain C.next n)
coordinates zero = ss zz
coordinates (suc n) = same-add (coordinates n) (next-same (coordinates n))
outputs : ∀ n → Same (next (chain next n)) (C.next (chain C.next n))
outputs n = next-same (coordinates n)
sums : ∀ n → Same
  (Ops.partial (T hz) (λ j → next (chain next j)) n)
  (Ops.partial (T hz) (λ j → C.next (chain C.next j)) n)
sums zero = outputs zero
sums (suc n) = same-add (sums n) (outputs (suc n))

first-feedback-component : Same (fold (M.sums 1)) C.output
first-feedback-component = ll sums

feedback≤mixed : C.output ≤ᵛ M.output
feedback≤mixed = ≤l 1 (same-value (same-sym first-feedback-component))

strict-floor≤mixed : hs C.a ≤ᵛ M.output
strict-floor≤mixed = ≤-trans V.strict-floor≤output feedback≤mixed
```

全混合的真实折叠输出已有 hs(flL P) 下界，且其中第1部分和的整条回灌
与已知合法闭项结构双模拟。本篇还未证明其余所有折叠部分和合法，
也没有用普通树值同余来处理 mixed 与原 θω 的关系。
