# 原节点全部真实采样的准入与值定位

这里的H、chain与diagonal均直接取原run的Ω方程。每个实际采样枝
在其统一合法世界中可入；枝的运行值进入原输出的完整部分和。后者
只用部分和包含当前项，不从源第一位置推导运行值单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSampleRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; Lg-flL; ixK; gcF; cxI)
open import OCF.Lean.LHRecLeg using (module New)
open import Data.Sum using (inj₂)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
import OCF.Lean.GeneralOmegaConsumeRun as R
open import OCF.Lean.GeneralOmegaSampleWorld
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.CountableCompletionRun using (right-add)

current-partial : ∀ (f : ℕ → Cd) n → f n ≤ᵛ Ops.partial S⊥ f n
current-partial f zero = ≤-refl _
current-partial f (suc n) = right-add (Ops.partial S⊥ f n) (f (suc n))

module Node (x : LH) (κ : K (Lv x)) (f : E (Lv x) κ → HB (Lv x)) where
  H : Cd → Cd
  H d = R.run x (f (code x κ d))
  feedback : ℕ → Cd
  feedback = chain H
  sample : ℕ → HB (Lv x)
  sample n = f (code x κ (feedback n))
  world : ℕ → Wd (Lv x)
  world n = World x (feedback n)
  world-legal : ∀ n → LgW (Lv x) (world n)
  world-legal n = legal x (feedback n)
  accessed : ∀ n → sample n ⊲[ world n ] hΩ κ f
  accessed n = hLim (admitted x κ (feedback n)) hself
  sample-legal : LgB (hΩ κ f) → ∀ n → LgB (sample n)
  sample-legal l n = proj₂ l (world-legal n) (admitted x κ (feedback n))
  sample-value : ∀ n → R.run x (sample n) ≤ᵛ R.run x (hΩ κ f)
  sample-value n = ≤l n (current-partial (λ j → H (feedback j)) n)

  -- 下面的比较仍显式以完成反馈的右项作为公共界，未假设链步进。
  bounded-source : ∀ {n m} → leg (feedback n) ⊲ leg (feedback m) →
    sample n ⊲[ world m ] hΩ κ f
  bounded-source {n} p = hLim (Bd↑ (Lv x) (growth x p) (admitted x κ (feedback n))) hself
  branches-step : LgB (hΩ κ f) → ∀ {n m} →
    leg (feedback n) ⊲ leg (feedback m) → sample n ⊲[ world m ] sample m
  branches-step l {n} {m} p = proj₁ l (world-legal m)
    (Bd↑ (Lv x) (growth x p) (admitted x κ (feedback n)))
    (admitted x κ (feedback m)) (position x κ p)

module Floor (k : LH) (g : HB (Lv k) → LH) where
  f : HB (Lv k) → HB (Lv (lΩ k g))
  f = New.θ (cxI k g) (gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d))))
  module Actual = Node (lΩ k g) ixK f
  sample-legal : ∀ n → LgB (Actual.sample n)
  sample-legal = Actual.sample-legal (Lg-flL (lΩ k g))
  sample-value : ∀ n → R.run (lΩ k g) (Actual.sample n) ≤ᵛ R.run (lΩ k g) (flL (lΩ k g))
  sample-value = Actual.sample-value
```

Floor实例覆盖任意原lΩ地板（包括含Ω指标），而不是只常值分支。
原代码采样的全部n都得到合法源枝与完整节点值下界；没有推出任意
可入枝也被采样，亦没有把branches-step转成run单调。
