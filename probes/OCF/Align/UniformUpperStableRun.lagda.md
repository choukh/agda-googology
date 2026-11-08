# 稳定采样关系的原折叠语义

context消费真实前缀定理，传递保留当前种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperStableRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (mul-≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
open import OCF.Align.UniformUpperStableIf
import OCF.Align.BoundedCompletionTerminalValueRun as V
import OCF.Align.UniformUpperPrefix as Prefix
open import OCF.Lean.Fold1Base using (≤-trans; ≤-refl)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (seed-mono; floor-self)
open import OCF.Align.UniformAcceptUpperRelation using (actual-zero-value)
import OCF.Align.BoundedNativeTerminalReady as T

eval : ∀ {a b} → Core a b → ∀ {u v} → u ≤ᵛ v →
  T.fold u a ≤ᵛ T.fold v b
eval (lift p) uv = V.eval p uv
eval (succ p) uv = l≤ (λ n → ≤l n (mul-≤ (eval p uv) n))
eval (right p) uv = ≤l 0 (eval p uv)
eval (all p) uv = l≤ (λ n → eval (p n) uv)
eval (pick n p) uv = ≤l n (eval p uv)
eval (omega {f} {g} p) {u} {v} uv = l≤ (λ n → ≤l n (sums n))
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
eval (uniform p) {v = v} uv = ≤l 0 (eval (p v) uv)

eval unit {u} {v} uv = ≤-trans (actual-zero-value u) (seed-mono floor-self uv)

eval (context {b = b} p bb) {v = v} uv = ≤-trans
  (l≤ (λ n → ≤l n (mul-≤ (eval p uv) n))) (Prefix.Prefix.repeated≤whole b bb v)
eval (through bb p q) {u} {v} uv = ≤-trans (eval p uv) (eval q (≤-refl v))
```
