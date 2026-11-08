# 原θ-path在seed世界域也不能保证步进

强化构造侧原θ常值极限实例；目标仍是lim(const2)，但世界改为真实seed域。
新增kind的界为1，因此同时处理坐标0和1，而不是只检查全零界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedThetaRouteNegGood where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeReadyGood using (Good)
import OCF.Align.BoundedThetaRouteLimit as X

V : Wd (Native X.B)
V = seed X.B (tt , hz)

base-kind : K (Native X.B)
base-kind = 0 , inj₁ (inj₁ (inj₂ tt))

no-zero : X.branch 0 ⊲[ V ] hz → ⊥
no-zero ()
no-one : X.branch 0 ⊲[ V ] hs hz → ⊥
no-one (hsuc p) = no-zero p

no-sum : ∀ (g : Cd → HB (Native X.B)) → g hz ≡ hs hz → ∀ n →
  X.branch 0 ⊲[ V ] Ops.partial (Native X.B) (λ _ → hΩ base-kind g) n → ⊥
no-sum g eq zero (hLim hself p) rewrite eq = no-one p
no-sum g eq (suc n) (hLim hself p) rewrite eq with p
... | hsuc q = no-sum g eq n q

no-repeat : ∀ (g : Cd → HB (Native X.B)) → g hz ≡ hs hz →
  X.branch 0 ⊲[ V ] Ops.repeat (Native X.B) (hΩ base-kind g) → ⊥
no-repeat g eq (hlim n p) = no-sum g eq n p

no-step : X.branch 0 ⊲[ V ] X.branch 1 → ⊥
no-step (hLim hself p) = no-repeat _ refl p
no-step (hLim (hsuc hself) (hLim hself p)) = no-one p

no-good-output : Good X.B X.output → ⊥
no-good-output l = no-step (proj₁ l (tt , tt) 0)
```

本篇输入、路径和共同高度完全来自BoundedThetaRouteLimit的原θ与θ-path。
它否定该原调用的Good，不能推断合法化采样leg的所有分支或目标0失败。
