# 原末段折叠的联合值比较

本篇实现冻结接口，比较的输出逐字是原T.fold。Ω处同时比较全部真实
坐标、当前界、输出和部分和，不把高层裸值序直接送过折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValueRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (mul-≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
open import OCF.Align.BoundedCompletionTerminalValueIf
import OCF.Align.BoundedNativeTerminalReady as T

eval : ∀ {a b} → VRel a b → ∀ {u v} → u ≤ᵛ v →
  T.fold u a ≤ᵛ T.fold v b
eval vz uv = terminal-positive _ _
eval (vs p) uv = l≤ (λ n → ≤l n (mul-≤ (eval p uv) n))
eval (vr p) uv = ≤l 0 (eval p uv)
eval (vl p) uv = l≤ (λ n → eval (p n) uv)
eval (vli n p) uv = ≤l n (eval p uv)
eval (vo {f} {g} p) {u} {v} uv = l≤ (λ n → ≤l n (sums n))
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
eval (vor p) {v = v} uv = ≤l 0 (eval (p v) uv)

instance-comparison : TerminalComparison
instance-comparison = record { compare = eval }
```

零规则只用原fold对所有raw输入输出至少1的已证事实。vor只取统一
下界在实际初界v处的实例；没有挑选其它分支，也没有Ω左消去规则。
