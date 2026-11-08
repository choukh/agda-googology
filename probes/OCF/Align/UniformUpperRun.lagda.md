# 新采样关系的原折叠语义

保持原Col的当前界、坐标和输出部分和；新增base使用已证实际值比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (mul-≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
open import OCF.Align.UniformUpperIf
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (seed-mono; floor-self)
open import OCF.Align.UniformAcceptUpperRelation using (actual-zero-value)
import OCF.Align.BoundedNativeTerminalReady as T

eval : ∀ {a b} → Rel a b → ∀ {u v} → u ≤ᵛ v →
  T.fold u a ≤ᵛ T.fold v b
eval rz uv = terminal-positive _ _
eval (rs p) uv = l≤ (λ n → ≤l n (mul-≤ (eval p uv) n))
eval (rr p) uv = ≤l 0 (eval p uv)
eval (rl p) uv = l≤ (λ n → eval (p n) uv)
eval (ri n p) uv = ≤l n (eval p uv)
eval (ro {f} {g} p) {u} {v} uv = l≤ (λ n → ≤l n (sums n))
  where
  module L = T.Orbit u f
  module R = T.Orbit v g
  coordinates : ∀ n → L.C.ce n ≤ᵛ R.C.ce n
  outputs : ∀ n → L.C.oo n ≤ᵛ R.C.oo n
  coordinates zero = uv
  coordinates (suc n) = add-mono (coordinates n) (outputs n)
  outputs n rewrite L.current n | R.current n = eval (p (coordinates n)) (coordinates n)
  sums : ∀ n → L.C.oO n ≤ᵛ R.C.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
eval (ru p) {v = v} uv = ≤l 0 (eval (p v) uv)

eval base {u} {v} uv = ≤-trans (actual-zero-value u) (seed-mono floor-self uv)

instance-comparison : SamplingComparison
instance-comparison = record { evaluate = λ r p → eval r p }
```
