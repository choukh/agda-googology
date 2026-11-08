# 累加完成保留左前缀，全部原链完成坐标逐点步进

ℕ极限只选择完成后第0部分和，那里原左前缀仍字面存在。任意H都
可用本定理，不要求H单调、H输出合法或原坐标全局可比。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaLegPrefixRun where
open import Data.Nat using (zero; suc; _≤′_; ≤′-refl; ≤′-step; _≤_)
open import Data.Nat.Properties using (≤⇒≤′)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.GeneralOmegaLegPrefixIf

complete-prefix : ∀ a b → leg a ⊲ leg (a ⊞ b)
complete-prefix a hz = hself
complete-prefix a (hs b) = hsuc (complete-prefix a b)
complete-prefix a (hl f) = hlim zero (complete-prefix a (f zero))
complete-prefix a (hΩ () f)
sample-step : ∀ (H : Cd → Cd) n → leg (chain H n) ⊲ leg (chain H (suc n))
sample-step H n = complete-prefix (chain H n) (H (chain H n))

sample-steps : ∀ H {j n} → j ≤′ n → leg (chain H j) ⊲ leg (chain H n)
sample-steps H ≤′-refl = hself
sample-steps H (≤′-step {n = n} p) = ⊲ᴮ-tr (sample-steps H p) (sample-step H n)
sample-indexed : ∀ H {j n} → j ≤ n → leg (chain H j) ⊲ leg (chain H n)
sample-indexed H p = sample-steps H (≤⇒≤′ p)
sample-legal : ∀ (H : Cd → Cd) n → LgB (leg (chain H n))
sample-legal H n = Lg-leg (chain H n)

instance-prefix : PrefixLaw
instance-prefix = record { complete-prefix = complete-prefix; sample-step = sample-step }
```

较早与较后样本直接共享较后完成坐标这一合法字面上界。这个结论不
允许将原树上任意第一位置穿过leg；也不宣称源节点任意枝被run访问。
