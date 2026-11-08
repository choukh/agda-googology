# 零前缀与原从零重复列的完整Γ捕获

先把零前缀高度的原合法证逐点配齐，再消费完整异层观察定理。
从零重复列的第1完成分量是0⊞leg a，因此这次可以捕获原Γ a；
不将它套到首项非零的任意NoSum列。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeActual where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (floor; leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCanonical using (collapse; actual-Γ-component)
open import OCF.Lean.GeneralOmegaCountableRegularClosure using (zero-add)
open import OCF.Lean.GeneralOmegaCountableShapeIf
open import OCF.Lean.GeneralOmegaCountableShapeBase
open import OCF.Lean.GeneralOmegaCountableShapeCompare
open import OCF.Lean.GeneralOmegaCountableShapeFloor
open import OCF.Lean.GeneralOmegaCountableShapeRun
open import OCF.Lean.FrozenWorldLift using (Same; same-sym; same-value)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)

zero-prefix-path : ∀ {a B : Cd} (p : a ⊲ B) →
  Paths (zero-add a) (zero-add B) (⊞-⊲ hz p) p
zero-prefix-path {a} hself = phere (zero-add a)
zero-prefix-path (hsuc p) = pnext (zero-prefix-path p)
zero-prefix-path (hlim n p) = plimit n (zero-prefix-path p)
zero-prefix-path (hLim {κ = ()} e p)
zero-prefix-legal : ∀ a (la : LgB a) →
  LegalShape (zero-add a) (Lg-⊞ hz a tt la) la
zero-prefix-legal hz la = tt
zero-prefix-legal (hs a) la = zero-prefix-legal a la
zero-prefix-legal (hl f) (st , sub) = (λ n → zero-prefix-path (st n)) , (λ n → zero-prefix-legal (f n) (sub n))
zero-prefix-legal (hΩ () f) la
collapse-zero-prefix : ∀ a la →
  Same (collapse (hz ⊞ a) (Lg-⊞ hz a tt la)) (collapse a la)
collapse-zero-prefix a la = leg-same (zero-tree
  (Observe.preserve (zero-add a) (Lg-⊞ hz a tt la) la (zero-prefix-legal a la)
    (floor-tree (zero-add a)) _ (zero-paths (zero-add a))))
Γ-zero-prefix : ∀ a → Same (Γ (hz ⊞ a)) (Γ a)
Γ-zero-prefix a = Γ-same (zero-add a)
Γ-zero-prefix-lower : ∀ a → Γ a ≤ᵛ Γ (hz ⊞ a)
Γ-zero-prefix-lower a = same-value (same-sym (Γ-zero-prefix a))
Γ-zero-prefix-upper : ∀ a → Γ (hz ⊞ a) ≤ᵛ Γ a
Γ-zero-prefix-upper a = same-value (Γ-zero-prefix a)

Γ-repeat-capture : ∀ a → Γ a ≤ᵛ Γ (hl (leftMul a))
Γ-repeat-capture a = ≤-trans
  (same-value (same-sym (collapse-zero-prefix (leg a) (Lg-leg a))))
  (actual-Γ-component (leftMul a) 1)
```

Γ-repeat-capture是全域实际输入定理，不只是有限测试或零实例。
它使用原重复列全部Γ输出，第1完成高度分量给完整原Γ a下界。
任意NoSum若第0项非零，将产生非零高度左前缀，不能援用此处
零前缀同形消去；一般高度右吸收仍独立。
