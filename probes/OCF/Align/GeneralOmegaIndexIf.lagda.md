# 原指标地板的前缀与完整回灌接口

直接使用LHRecFl的New.θ；不改源地板或新消费者。参数k,g是原层结构，
不是为某个站定制的替代模型。以下不比较两个下标、不选槽或判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexIf where
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; gcF; cxI)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

θ : ∀ k (g : HB (Lv k) → LH) → HB (Lv k) → HB (Lv (lΩ k g))
θ k g = New.θ (cxI k g) (gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d))))
branch : ∀ k g → HB (Lv (lΩ k g)) → Cd → Cd
branch k g A d = run (lΩ k g) (A ⊞ θ k g (flL k ⊞ pure (Lv k) (leg d)))
base : ∀ k g → HB (Lv (lΩ k g)) → Cd
base k g A = run (lΩ k g) (A ⊞ θ k g (flL k))

record IndexBound : Set₁ where
  field
    suffix : ∀ k g A a d → run (lΩ k g) (A ⊞ θ k g a) ≤ᵛ
      run (lΩ k g) (A ⊞ θ k g (a ⊞ pure (Lv k) d))
    outputs : ∀ k g A n → base k g A ≤ᵛ branch k g A (chain (branch k g A) n)
    whole : ∀ k g A → Ops.repeat S⊥ (base k g A) ≤ᵛ run (lΩ k g) (A ⊞ flL (lΩ k g))
    first : ∀ k g A →
      run (lΩ k g) (A ⊞ (θ k g (flL k) ⊞ ι {IxL k} {FXL k g} (inj₂ (flL k)) (flL (g (flL k))))) ≤ᵛ
      run (lΩ k g) (A ⊞ flL (lΩ k g))
```

whole须覆盖原全部输出和；first保留原第一次编码里的完整分量地板。
当k=lz时base只剩run A，故whole单独不代表塔强度提升；需要继续分析
first中的实际分量嵌入，不能假定run保任意Same或右加法。
