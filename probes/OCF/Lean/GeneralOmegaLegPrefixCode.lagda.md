# 实际code低层载荷的合法性与共同样本界

code的载荷是原低层地板加pure(leg反馈)。纯树运输完成前缀路径，
同一个原floor左加法运输它，得到原所有kind的实际样本有界路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaLegPrefixCode where
open import Data.Nat using (suc; _≤_)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.GeneralOmegaLegPrefixRun using (sample-step; sample-indexed)

pure-position : ∀ S {a b w} → a ⊲ b → pure S a ⊲[ w ] pure S b
pure-position S hself = hself
pure-position S (hsuc p) = hsuc (pure-position S p)
pure-position S (hlim n p) = hlim n (pure-position S p)
pure-position S (hLim {κ = ()} e p)
pure-legal : ∀ S a → LgB a → LgB (pure S a)
pure-legal S hz l = tt
pure-legal S (hs a) l = pure-legal S a l
pure-legal S (hl f) (st , lf) = (λ n → pure-position S (st n)) , (λ n → pure-legal S (f n) (lf n))
pure-legal S (hΩ () f) l

payload : ∀ x κ → Cd → HB (Lv (lvl x κ))
payload x κ d = flL (lvl x κ) ⊞ pure (Lv (lvl x κ)) (leg d)
payload-legal : ∀ x κ d → LgB (payload x κ d)
payload-legal x κ d = Lg-⊞ _ _ (Lg-flL (lvl x κ))
  (pure-legal (Lv (lvl x κ)) (leg d) (Lg-leg d))
payload-step : ∀ x κ (H : Cd → Cd) n {w} →
  payload x κ (chain H n) ⊲[ w ] payload x κ (chain H (suc n))
payload-step x κ H n = ⊞-⊲ (flL (lvl x κ)) (pure-position (Lv (lvl x κ)) (sample-step H n))
payload-indexed : ∀ x κ (H : Cd → Cd) {j n w} → j ≤ n →
  payload x κ (chain H j) ⊲[ w ] payload x κ (chain H n)
payload-indexed x κ H p = ⊞-⊲ (flL (lvl x κ)) (pure-position (Lv (lvl x κ)) (sample-indexed H p))
```

payload-indexed在任意同一低层world中成立，右树payload-legal无前提。
把载荷变回原E坐标、在原KS世界中给Bd仍须由实际world实例完成；
这不自动给跨不同kind比较或run输出单调。
