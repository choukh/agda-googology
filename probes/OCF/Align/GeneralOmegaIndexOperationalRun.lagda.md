# 原运行上下文中的捕获与完成稳定

所有语义对象逐字为run(read 原树)。等式只来自已实例化的Context
构造子方程；没有把任意Same送过run。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexOperationalRun where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ixK)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.HigherIndexConsumePositive using (mul-partial)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenAbsorbNegUpper using (P; infl)
open import OCF.Align.GeneralOmegaConsumeValuePure using (positive)
open import OCF.Align.GeneralOmegaIndexIf using (θ)
open import OCF.Align.GeneralOmegaIndexRaise
open import OCF.Align.GeneralOmegaIndexOperationalIf
open import OCF.Lean.GeneralOmegaCompletionIf using (Capture)
import OCF.Lean.GeneralOmegaCompletionRun as Complete

module Mapped {x y} (j : Context x y) where
  prefix-value : ∀ B C → run y (read j B) ≤ᵛ run y (read j (B ⊞ C))
  prefix-value B hz = ≤-refl _
  prefix-value B (hs C) rewrite r-s j (B ⊞ C) = ≤l 0 (prefix-value B C)
  prefix-value B (hl f) rewrite r-l j (λ n → B ⊞ f n) = ≤l 0 (prefix-value B (f 0))
  prefix-value B (hΩ κ f) rewrite r-Ω j κ (λ e → B ⊞ f e) =
    ≤l 0 (prefix-value B (f (pull j κ (code y (kind j κ) (hs hz)))))
  repeated : ∀ B {C} → Raises C →
    Ops.repeat S⊥ (run y (read j B)) ≤ᵛ run y (read j (B ⊞ C))
  repeated B (successor {a}) rewrite r-s j (B ⊞ a) = repeat-mono (prefix-value B a)
  repeated B (limit {f} n p) rewrite r-l j (λ n → B ⊞ f n) = ≤l n (repeated B p)
  repeated B (omega {κ} {g}) rewrite r-Ω j κ (λ e → B ⊞ g e) = l≤ (λ n → ≤l n (parts n))
    where
    H : Cd → Cd
    H d = run y (read j (B ⊞ g (pull j κ (code y (kind j κ) d))))
    parts : ∀ n → Ops.partial S⊥ (λ _ → run y (read j B)) n ≤ᵛ
      Ops.partial S⊥ (λ n → H (chain H n)) n
    parts zero = prefix-value B _
    parts (suc n) = add-mono (parts n) (prefix-value B _)

module Raised (k : LH) (g : HB (Lv k) → LH) {y}
  (j : Context (lΩ k g) y) (raising : ∀ e → Raises (flL (g e))) where
  affine : ∀ a d → P (run y (read j (θ k g a))) d ≤ᵛ
    run y (read j (θ k g (a ⊞ pure (Lv k) d)))
  affine a hz = ≤-refl _
  affine a (hs d) = ≤-trans (l≤ (λ n → ≤l n (mul-partial (affine a d) n)))
    (Mapped.repeated j (θ k g (a ⊞ pure (Lv k) d))
      (raises-ι (inj₂ (a ⊞ pure (Lv k) d)) (raising (a ⊞ pure (Lv k) d))))
  affine a (hl f) rewrite r-l j (λ n → θ k g (a ⊞ pure (Lv k) (f n))) =
    l≤ (λ n → ≤l n (affine a (f n)))
  H : Cd → Cd
  H d = run y (read j (θ k g (pull j ixK (code y (kind j ixK) d))))
  captures : ∀ d → leg d ≤ᵛ H d
  captures d rewrite back j ixK d = ≤-trans
    (infl (run y (read j (θ k g (flL k)))) (positive y (read j (θ k g (flL k)))) (leg d))
    (affine (flL k) (leg d))
  captured : Capture H
  captured = record { on-chain = λ n → captures (chain H n) }
  stable : leg (run y (read j (flL (lΩ k g)))) ≤ᵛ run y (read j (flL (lΩ k g)))
  stable rewrite r-Ω j ixK (θ k g) = Complete.Result.upper H captured

module Successor (k y : LH) (j : Context (ΩL (ls k)) y) = Raised k (λ e → ΩL k ⊕L upL k e) j
  (λ e → floor-raises (plus-shape (Ω-shape k) (upL k e)))
module Index (k : LH) (g : HB (Lv k) → LH) (y : LH)
  (j : Context (ΩL (lΩ k g)) y) = Raised k (λ e → ΩL (g e)) j (λ e → floor-raises (Ω-shape (g e)))

module Next (k y : LH) (j : Context (ls k) y) where
  affine : ∀ a d → P (run y (read j (up a))) d ≤ᵛ
    run y (read j (up (a ⊞ pure (Lv k) d)))
  affine a hz = ≤-refl _
  affine a (hs d) rewrite r-s j (up (a ⊞ pure (Lv k) d)) =
    l≤ (λ n → ≤l n (mul-partial (affine a d) n))
  affine a (hl f) rewrite r-l j (λ n → up (a ⊞ pure (Lv k) (f n))) =
    l≤ (λ n → ≤l n (affine a (f n)))
  H : Cd → Cd
  H d = run y (read j (up (pull j (inj₂ tt) (code y (kind j (inj₂ tt)) d))))
  captures : ∀ d → leg d ≤ᵛ H d
  captures d rewrite back j (inj₂ tt) d = ≤-trans
    (infl (run y (read j (up (flL k)))) (positive y (read j (up (flL k)))) (leg d))
    (affine (flL k) (leg d))
  captured : Capture H
  captured = record { on-chain = λ n → captures (chain H n) }
  stable : leg (run y (read j (flL (ls k)))) ≤ᵛ run y (read j (flL (ls k)))
  stable rewrite r-Ω j (inj₂ tt) up = Complete.Result.upper H captured
```

Next处理原ls地板；Successor/Index处理ΩL两种指标规则。任意真实
prefix与直接ι可由Context.compose装配，因此不再存在put替换原ι的缺口。
