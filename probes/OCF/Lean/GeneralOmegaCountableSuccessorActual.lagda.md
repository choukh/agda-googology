# 原Γ在输入后继上的严格一步界

完成运输只使用整树Same与leg-same，不使用一般≤穿leg。完成列
第1部分和含Γ c和下一正项，故得到hs(Γ c)的下界。此律针对输入
hs c，不能拿任意c≤d推出Γ c≤Γ d。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableSuccessorActual where
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (rawΓ; Γ; positive)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
import OCF.Lean.GeneralOmegaCountableSuccessorIf as I
open import OCF.Lean.GeneralOmegaCountableSuccessorRun using (whole; gamma-whole; gamma-lower)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l; ≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

completed-shape : ∀ c → Same (Γ (hs c))
  (leg (hl (I.At.read-orbit (leg c) (Lg-leg c))))
completed-shape c = leg-same (gamma-whole c)

raw-successor : ∀ c → rawΓ c ≤ᵛ rawΓ (hs c)
raw-successor c = ≤-trans (≤l 0 (≤-refl (rawΓ c))) (gamma-lower c)

module At (c : Cd) where
  module S = I.At (leg c) (Lg-leg c)
  next-positive : hs hz ≤ᵛ leg (S.read-orbit 1)
  next-positive = ≤-trans
    (positive (leg c) (Lg-leg c) (z⊲ᴮ (leg c)) (S.P.NoSum 1))
    (inflation (S.read-orbit 1))
  completed-first : hs (Γ c) ≤ᵛ leg (hl S.read-orbit)
  completed-first = ≤l 1 (⊞-≤ʳ (Γ c) next-positive)

strict-successor : ∀ c → hs (Γ c) ≤ᵛ Γ (hs c)
strict-successor c = ≤-trans (At.completed-first c)
  (same-value (same-sym (completed-shape c)))
successor : ∀ c → Γ c ≤ᵛ Γ (hs c)
successor c = ≤-trans (≤s (≤-refl (Γ c))) (strict-successor c)
not-back : ∀ c → Γ (hs c) ≤ᵛ Γ c → ⊥
not-back c p = ¬s≤ᵛ (Γ c) (≤-trans (strict-successor c) p)

-- 真实非有限公共高度，保留原ω的全部累计floor分量。
omega-whole : Same
  (observe (hs omega) omega-legal hz (hsuc (z⊲ᴮ omega)) (floor (hs omega)))
  (hl (I.At.read-orbit omega omega-legal))
omega-whole = whole omega omega-legal
```

已证全c严格后继一步及B=ω完整公式；所有前提均来自原leg合法性或
omega-legal。尚未得到Γ迭代阶段之间的比较，因为stage(suc n)=Γ(stage n)
不等于hs(stage n)。也没有由此得到新的记号强度或EBO终点验收。
