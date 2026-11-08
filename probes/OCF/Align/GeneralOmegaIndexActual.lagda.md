# 原ΩL两种指标分支的完成坐标捕获

保持全部New.θ前缀与code中的leg。仅对每个实际分量地板具有Raises
的族给出捕获；原ΩL的后继规则和指标规则均有统一结构实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexActual where
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.HigherIndexConsumePositive using (mul-partial)
open import OCF.Align.FrozenAbsorbNegUpper using (P; infl)
open import OCF.Align.GeneralOmegaConsumeValuePure using (positive)
open import OCF.Align.GeneralOmegaIndexIf
open import OCF.Align.GeneralOmegaIndexRaise

module Raised (k : LH) (g : HB (Lv k) → LH)
  (raising : ∀ e → Raises (flL (g e))) where
  affine : ∀ A a d → P (run (lΩ k g) (A ⊞ θ k g a)) d ≤ᵛ
    run (lΩ k g) (A ⊞ θ k g (a ⊞ pure (Lv k) d))
  affine A a hz = ≤-refl _
  affine A a (hs d) = ≤-trans
    (l≤ (λ n → ≤l n (mul-partial (affine A a d) n)))
    (repeat-context (lΩ k g) A (θ k g (a ⊞ pure (Lv k) d))
      (raises-ι (inj₂ (a ⊞ pure (Lv k) d)) (raising (a ⊞ pure (Lv k) d))))
  affine A a (hl f) = l≤ (λ n → ≤l n (affine A a (f n)))

  captures : ∀ A d → leg d ≤ᵛ branch k g A d
  captures A d = ≤-trans
    (infl (base k g A) (positive (lΩ k g) (A ⊞ θ k g (flL k))) (leg d))
    (affine A (flL k) (leg d))

module Successor (k : LH) = Raised k (λ e → ΩL k ⊕L upL k e)
  (λ e → floor-raises (plus-shape (Ω-shape k) (upL k e)))
module Index (k : LH) (g : HB (Lv k) → LH) = Raised k (λ e → ΩL (g e))
  (λ e → floor-raises (Ω-shape (g e)))
```

Successor正是ΩL(ls k)原族，Index正是ΩL(lΩ k g)原族。captures
量化全部实际raw反馈d及任意源前缀A，不是只对链首项成立。没有改
code、θ、diagonal或原floor；g=0一般不满足raising，不能免费套用。

本结论可供完成闭包稳定性定理消费，但尚未把外层ΛL所有累计分量
一起送过最终leg，也没有给EBO序数值下界。
