# 对全部LH的后继地板计算与严格值界

纯尾结构使实际后继回调的异坐标Same可证；完整链比较复用已冻结的
BoundedDiagonalSame，不对任意Ω分支假设Same同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaConsumeLayerRun where
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans; ⊞-≤ʳ)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.LHRecTy using (LH; Lv; ls; ll)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeLayerIf
open import OCF.Lean.BoundedDiagonalSame using (same-refl; same-add)
import OCF.Lean.BoundedDiagonalSame as D
open import OCF.Lean.TowerCollapseIf using (module Ops)
import OCF.Lean.BoundedMixedAffine as Aff
import OCF.Lean.GeneralOmegaConsumeRun as R

positive : ∀ x a → hs hz ≤ᵛ R.run x a
positive x hz = s≤s z≤
positive x (hs a) = ≤l 0 (positive x a)
positive x (hl f) = ≤l 0 (positive x (f 0))
positive x (hΩ κ f) = ≤l 0 (positive x (f (code x κ (hs hz))))

same-trans : ∀ {a b c : Cd} → Same a b → Same b c → Same a c
same-trans zz zz = zz
same-trans (ss p) (ss q) = ss (same-trans p q)
same-trans (ll p) (ll q) = ll (λ n → same-trans (p n) (q n))

partial-same : ∀ {f g : _ → Cd} → (∀ n → Same (f n) (g n)) → ∀ n →
  Same (Ops.partial S⊥ f n) (Ops.partial S⊥ g n)
partial-same p zero = p zero
partial-same p (suc n) = same-add (partial-same p n) (p (suc n))

leg-same : ∀ {a b : Cd} → Same a b → Same (C.leg a) (C.leg b)
leg-sums : ∀ {f g : _ → Cd} → (∀ n → Same (f n) (g n)) → ∀ n →
  Same (C.Σ₀ (λ j → C.leg (f j)) n) (C.Σ₀ (λ j → C.leg (g j)) n)
leg-same zz = zz
leg-same (ss p) = ss (leg-same p)
leg-same (ll p) = ll (leg-sums p)
leg-sums p zero = leg-same (p zero)
leg-sums p (suc n) = same-add (leg-sums p n) (leg-same (p (suc n)))

act-same : ∀ {a b d e : Cd} → Same a b → Same d e →
  Same (Aff.Action.run S⊥ a d) (Aff.Action.run S⊥ b e)
act-same p zz = p
act-same p (ss q) = ll (partial-same (λ _ → act-same p q))
act-same p (ll q) = ll (λ n → act-same p (q n))

pure-prefix : ∀ x (a : HB (Lv x)) d → Same
  (R.run (ls x) (up (a ⊞ pure (Lv x) d)))
  (Aff.Action.run S⊥ (R.run (ls x) (up a)) d)
pure-prefix x a hz = same-refl _
pure-prefix x a (hs d) = ll (partial-same (λ _ → pure-prefix x a d))
pure-prefix x a (hl f) = ll (λ n → pure-prefix x a (f n))
pure-prefix x a (hΩ () f)

callback : ∀ x {d e} → Same d e → Same
  (R.run (ls x) (up (flL x ⊞ pure (Lv x) (C.leg d)))) (H (A x) e)
callback x {d} p = same-trans (pure-prefix x (flL x) (C.leg d))
  (act-same (same-refl (A x)) (leg-same p))

whole : ∀ x → Same (R.run (ls x) (flL (ls x))) (closure (A x))
whole x = D.Compare.result
  (λ d → R.run (ls x) (up (flL x ⊞ pure (Lv x) (C.leg d)))) (H (A x))
  (λ d → R.run (ls x) (up (flL x ⊞ pure (Lv x) (C.leg d)))) (H (A x))
  (callback x) (callback x)

closure-strict : ∀ a → hs hz ≤ᵛ a → hs a ≤ᵛ closure a
closure-strict a p = ≤l 0 (≤l 1 (⊞-≤ʳ a p))
strict-step : ∀ x → hs (A x) ≤ᵛ R.run (ls x) (flL (ls x))
strict-step x = ≤-trans (closure-strict (A x) (positive (ls x) (up (flL x))))
  (same-value (same-sym (whole x)))
not-bounded-by-prefix : ∀ x → R.run (ls x) (flL (ls x)) ≤ᵛ A x → ⊥
not-bounded-by-prefix x p = ¬s≤ᵛ (A x) (≤-trans (strict-step x) p)

instance-successor : SuccessorLayer
instance-successor = record { whole = whole ; strict-step = strict-step }

-- 同一源层中真实前缀不会丢失；Ω仅选择原seed1首输出，不比较异坐标。
prefix-position : ∀ x a b → R.run x a ⊲ R.run x (a ⊞ b)
prefix-position x a hz = hself
prefix-position x a (hs b) = hlim 0 (prefix-position x a b)
prefix-position x a (hl f) = hlim 0 (prefix-position x a (f 0))
prefix-position x a (hΩ κ f) = hlim 0 (prefix-position x a (f (code x κ (hs hz))))

limit-step : ∀ f n → R.run (ll f) (ΣF f n) ⊲ R.run (ll f) (ΣF f (suc n))
limit-step f n = prefix-position (ll f) (ΣF f n) _
```

whole是全部LH后继结构参数的一步完整输出定理；strict-step严格超过
同层实际嵌入前缀A x。未把A x换成run x(flL x)，所以尚未给跨层迭代
支配或EBO下界。limit-step只给原ℕ层部分和输出的第一位置步进，不声称
任意raw输入的run保合法、超可加或跨注入值同余。
