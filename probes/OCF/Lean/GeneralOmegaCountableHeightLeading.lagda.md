# 原完成保留前沿路径与Γ的左高度加法吸收

Leading在任意普通Cd上定义，允许任意非有限原分支。完成在第0
分量没有前置累计项，因此保留这些路径及其诱导合法证；全部左
加法前缀正好属于这个域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableHeightLeading where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableHeightIf
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableObservePosition using (position-collapse)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCanonical using (collapse)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

leg-leading : ∀ {a B} → Leading a B → Leading (leg a) (leg B)
leg-leading here = here
leg-leading (next p) = next (leg-leading p)
leg-leading (first p) = first (leg-leading p)
legal-leading : ∀ {a B} (p : Leading a B) →
  lgB⊲ (path (leg-leading p)) tt (Lg-leg B) ≡ Lg-leg a
legal-leading here = refl
legal-leading (next p) = legal-leading p
legal-leading (first p) = legal-leading p
instance-leading : LeadingCompletion
instance-leading = record { keep-completed = leg-leading }
Γ-leading : ∀ {a B} → Leading a B → Γ a ≤ᵛ Γ B
Γ-leading {a} {B} p = subst (λ la → collapse (leg a) la ≤ᵛ Γ B)
  (legal-leading p) (position-collapse (Lg-leg B) (path (leg-leading p)))

prefix-leading : ∀ (a b : Cd) → Leading a (a ⊞ b)
prefix-leading a hz = here
prefix-leading a (hs b) = next (prefix-leading a b)
prefix-leading a (hl f) = first (prefix-leading a (f zero))
prefix-leading a (hΩ () f)
Γ-left-add : ∀ (a b : Cd) → Γ a ≤ᵛ Γ (a ⊞ b)
Γ-left-add a b = Γ-leading (prefix-leading a b)
Γ-first-component : ∀ (f : ℕ → Cd) → Γ (f zero) ≤ᵛ Γ (hl f)
Γ-first-component f = Γ-leading (first here)
Γ-completed-sum-step : ∀ (f : ℕ → Cd) n →
  Γ (Σ₀ (λ k → leg (f k)) n) ≤ᵛ Γ (Σ₀ (λ k → leg (f k)) (suc n))
Γ-completed-sum-step f n = Γ-left-add _ _
```

Γ-left-add比较原输入加法后的整个Γ，不是同一source的输出加法。
其共界证据实际为完成后Leading路径；所有合法性由原Lg-leg给出。
Γ-first-component覆盖原无限族的整个第0分量，未更换运行器或种子。
一般第n分量位于累计高度的右侧，不能由本篇左吸收推出；通用
BoundedHeightSimulation尚未实例化，也未声称Γ一般值单调。
