# 原全阶段覆盖无leg的纯反馈闭包

源参照只用P的有向单调性。目标leg仅通过d≤leg d出现，绝不把两个
有向相关的raw坐标直接送过leg。所有结论覆盖完整反馈链与部分和。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaStrengthRun where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; ΛL; twL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ixK)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Align.FrozenAbsorbNegUpper using (P; mono)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.GeneralOmegaStrengthIf
open import OCF.Align.GeneralOmegaIndexIf using (θ)
open import OCF.Align.GeneralOmegaIndexRaise
open import OCF.Align.GeneralOmegaIndexOperationalIf
open import OCF.Align.GeneralOmegaIndexOperationalActual using (Root; zero; one; index; tower-root; stage; context)
import OCF.Align.GeneralOmegaIndexOperationalRun as R

module Cover (a : Cd) (H : Cd → Cd) (action : ∀ d → P a d ≤ᵛ H d) where
  coordinates : ∀ n → chain (P a) n ≤ᵛ chain H n
  outputs : ∀ n → P a (chain (P a) n) ≤ᵛ H (chain H n)
  coordinates zero = ≤-refl _
  coordinates (suc n) = add-mono (coordinates n) (outputs n)
  outputs n = ≤-trans (mono (≤-refl a) (coordinates n)) (action (chain H n))
  sums : ∀ n → Ops.partial S⊥ (λ j → P a (chain (P a) j)) n ≤ᵛ
    Ops.partial S⊥ (λ j → H (chain H j)) n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
  whole : Close a ≤ᵛ diagonal H H
  whole = l≤ (λ n → ≤l n (sums n))

close-mono : ∀ {a b} → a ≤ᵛ b → Close a ≤ᵛ Close b
close-mono {a} {b} ab = Cover.whole a (P b) (λ d → mono ab (≤-refl d))

module Next (y : LH) (j : Context (ls lz) y) where
  action : ∀ d → P (run y (read j hz)) d ≤ᵛ R.Next.H lz y j d
  action d rewrite back j (inj₂ tt) d = ≤-trans
    (mono (≤-refl _) (inflation d)) (R.Next.affine lz y j hz (leg d))
  whole : Close (run y (read j hz)) ≤ᵛ run y (read j (flL (ls lz)))
  whole rewrite r-Ω j (inj₂ tt) up = Cover.whole _ (R.Next.H lz y j) action

module Index (g : Cd → LH) (y : LH) (j : Context (lΩ lz g) y)
  (raising : ∀ e → Raises (flL (g e))) where
  action : ∀ d → P (run y (read j hz)) d ≤ᵛ R.Raised.H lz g j raising d
  action d rewrite back j ixK d = ≤-trans
    (mono (≤-refl _) (inflation d)) (R.Raised.affine lz g j raising hz (leg d))
  whole : Close (run y (read j hz)) ≤ᵛ run y (read j (flL (lΩ lz g)))
  whole rewrite r-Ω j ixK (θ lz g) = Cover.whole _ (R.Raised.H lz g j raising) action

root-close : ∀ x → Root x → ∀ y (j : Context (ΩL x) y) →
  Close (run y (read j hz)) ≤ᵛ run y (read j (flL (ΩL x)))
root-close .lz zero y j = Next.whole y j
root-close .(ls lz) one y j = Index.whole _ y j
  (λ e → floor-raises (plus-shape (Ω-shape lz) (upL lz e)))
root-close .(lΩ lz g) (index g) y j = Index.whole _ y j
  (λ e → floor-raises (Ω-shape (g e)))
stage-close : ∀ n → Close (stage n) ≤ᵛ stage (suc n)
stage-close n = root-close (twL n) (tower-root n) ΛL (context n)
iteration : ∀ n → iterate n ≤ᵛ stage n
iteration zero = ≤-refl _
iteration (suc n) = ≤-trans (close-mono (iteration n)) (stage-close n)

instance-strength : Strength
instance-strength = record { stage-close = stage-close ; iteration = iteration }
```

stage-close与iteration都针对原stage全n，不是另造源层或替代输出。
标签参照γ的下一步仍需额外值桥，不能由本迭代下界推定。
