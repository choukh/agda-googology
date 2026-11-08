# 原θ纯扩展与指标Ω全部输出和

只使用左前缀在实际run中的支配。右侧若含Ω，取其真实初反馈1处
继续结构递归；没有对任意高层值序施加run单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.CRw using (leg)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.GeneralOmegaIndexIf

context-prefix : ∀ x (A B C : HB (Lv x)) →
  run x (A ⊞ B) ≤ᵛ run x (A ⊞ (B ⊞ C))
context-prefix x A B hz = ≤-refl _
context-prefix x A B (hs C) = ≤l 0 (context-prefix x A B C)
context-prefix x A B (hl f) = ≤l 0 (context-prefix x A B (f 0))
context-prefix x A B (hΩ κ f) = ≤l 0 (context-prefix x A B (f (code x κ (hs hz))))

suffix : ∀ k g A a d → run (lΩ k g) (A ⊞ θ k g a) ≤ᵛ
  run (lΩ k g) (A ⊞ θ k g (a ⊞ pure (Lv k) d))
suffix k g A a hz = ≤-refl _
suffix k g A a (hs d) = ≤-trans (suffix k g A a d)
  (context-prefix (lΩ k g) A (θ k g (a ⊞ pure (Lv k) d)) _)
suffix k g A a (hl f) = ≤l 0 (suffix k g A a (f 0))

outputs : ∀ k g A n → base k g A ≤ᵛ branch k g A (chain (branch k g A) n)
outputs k g A n = suffix k g A (flL k) (leg (chain (branch k g A) n))
sums : ∀ k g A n → Ops.partial S⊥ (λ _ → base k g A) n ≤ᵛ
  Ops.partial S⊥ (λ j → branch k g A (chain (branch k g A) j)) n
sums k g A zero = outputs k g A zero
sums k g A (suc n) = add-mono (sums k g A n) (outputs k g A (suc n))
whole : ∀ k g A → Ops.repeat S⊥ (base k g A) ≤ᵛ run (lΩ k g) (A ⊞ flL (lΩ k g))
whole k g A = l≤ (λ n → ≤l n (sums k g A n))

open import Data.Sum using (inj₂)
first : ∀ k g A →
  run (lΩ k g) (A ⊞ (θ k g (flL k) ⊞ ι {IxL k} {FXL k g} (inj₂ (flL k)) (flL (g (flL k))))) ≤ᵛ
  run (lΩ k g) (A ⊞ flL (lΩ k g))
first k g A = ≤l 0 (≤-refl _)

instance-index : IndexBound
instance-index = record { suffix = suffix ; outputs = outputs ; whole = whole ; first = first }
```

sums是对原部分和逐n的证明，目标仍为原code/run/chain。first在一般k
保留θ地板前缀，不能从它删除左前缀以推出右分量值界。
