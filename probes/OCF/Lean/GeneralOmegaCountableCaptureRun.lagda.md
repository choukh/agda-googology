# 原stage 2捕获全部有限参数输出

两次使用实际极限分量捕获，再规范零目标路径。数值高度的证据规范化
仅在num上证明，不要求一般合法性证据或路径无关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableCaptureRun where
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step)
import Data.Nat.Properties as N
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (floor)
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; rawΓ; stage; tree; stage-lower)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Lean.GeneralOmegaCountableNumber using (leg-num; path-unique)
open import OCF.Lean.GeneralOmegaCountableCapturePath using (sum; sum-large; second-sum)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCapture using (component-capture)
open import OCF.Lean.GeneralOmegaCountableObserveZeroPath using (zero-path-observe)
open import OCF.Lean.GeneralOmegaCountableRelRun using (floor-related)
open import OCF.Lean.GeneralOmegaCountableRelActual using (zero-same)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.GeneralOmegaCountableSuccessorActual using (successor)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)

legal-unique : ∀ n (p q : LgB (num n)) → p ≡ q
legal-unique zero tt tt = refl
legal-unique (suc n) p q = legal-unique n p q
normal : ∀ n {B} → B ≡ num n → (lB : LgB B) (pt : hz ⊲ B) →
  observe B lB hz pt (floor B) ≡ observe (num n) (num-legal n) hz (z⊲ᴮ (num n)) (floor (num n))
normal n refl lB pt rewrite legal-unique n lB (num-legal n) | path-unique n pt (z⊲ᴮ (num n)) = refl
finite-completed : ∀ n {B} → B ≡ num n → (lB : LgB B) (pt : hz ⊲ B) →
  Γ (num n) ≡ leg (observe B lB hz pt (floor B))
finite-completed n eq lB pt = cong leg (trans
  (normal n (leg-num n) (Lg-leg (num n)) (z⊲ᴮ (leg (num n))))
  (sym (normal n eq lB pt)))

children : Cd → ℕ → Cd
children hz n = hz
children (hs a) n = a
children (hl f) n = f n
children (hΩ () g) n
H = leg (stage 1)
lH = Lg-leg (stage 1)
f = children H
I = f 0
lI = proj₂ lH 0
g = children I
budget : ℕ → ℕ
budget n = sum (sum (λ j → j)) n
coordinate : ∀ n → g n ≡ num (budget n)
coordinate = second-sum

path-change : ∀ B lB pt qt →
  leg (observe B lB hz pt (floor B)) ≤ᵛ leg (observe B lB hz qt (floor B))
path-change B lB pt qt = same-value (leg-same (zero-same
  (zero-path-observe B lB pt qt (floor-related B))))

budget-capture : ∀ n → Γ (num (budget n)) ≤ᵛ stage 2
budget-capture n rewrite finite-completed (budget n) (coordinate n) (proj₂ lI n) (z⊲ᴮ (g n)) =
  ≤-trans (component-capture g lI n (z⊲ᴮ (g n)))
  (≤-trans (component-capture f lH 0 (hlim n (z⊲ᴮ (g n))))
    (path-change H lH (hlim 0 (hlim n (z⊲ᴮ (g n)))) (z⊲ᴮ H)))

numeric-mono′ : ∀ {m n} → m ≤′ n → Γ (num m) ≤ᵛ Γ (num n)
numeric-mono′ ≤′-refl = ≤-refl _
numeric-mono′ (≤′-step {n = n} p) = ≤-trans (numeric-mono′ p) (successor (num n))
numeric-mono : ∀ {m n} → m ≤ n → Γ (num m) ≤ᵛ Γ (num n)
numeric-mono p = numeric-mono′ (N.≤⇒≤′ p)
finite-capture : ∀ n → Γ (num n) ≤ᵛ stage 2
finite-capture n = ≤-trans (numeric-mono
  (N.≤-trans (sum-large (λ j → j) n) (sum-large (sum (λ j → j)) n))) (budget-capture n)
finite-in-tree : ∀ n → Γ (num n) ≤ᵛ tree
finite-in-tree n = ≤-trans (finite-capture n) (stage-lower 2)
```
