# 完成后的正则前缀闭包

Reg不是一般合法性的替代。这里只对Built实际输出证明完成闭包；
重复列的零项单独保留，后续正项才用于累计严格步进。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularClosure where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableRegularIf
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; ⊞-≤ʳ)
open import OCF.Lean.CountableCompletionRun using (right-add; inflation)

reg-same : ∀ {a b} → Same a b → Reg a → Reg b
reg-same zz r = tt
reg-same (ss p) r = reg-same p r
reg-same (ll p) (step , sub) =
  (λ n → ≤-trans (s≤s (same-value (same-sym (p n))))
    (≤-trans (step n) (same-value (p (suc n))))) , (λ n → reg-same (p n) (sub n))
reg-add : ∀ {a b} → Reg a → Reg b → Reg (a ⊞ b)
reg-add {b = hz} ra rb = ra
reg-add {b = hs b} ra rb = reg-add ra rb
reg-add {a} {hl f} ra (step , sub) = (λ n → ⊞-≤ʳ a (step n)) , (λ n → reg-add ra (sub n))

sum-reg : ∀ f → (∀ n → Reg (f n)) → ∀ n → Reg (Σ₀ f n)
sum-reg f r zero = r zero
sum-reg f r (suc n) = reg-add (sum-reg f r n) (r (suc n))
sum-limit : ∀ f → (∀ n → Reg (f n)) → (∀ n → hs hz ≤ᵛ f (suc n)) → Reg (hl (Σ₀ f))
sum-limit f r pos = (λ n → ⊞-≤ʳ (Σ₀ f n) (pos n)) , sum-reg f r
reg-leg : ∀ {a} → Reg a → Reg (leg a)
reg-leg {a = hz} r = tt
reg-leg {hs a} r = reg-leg r
reg-leg {hl f} (step , sub) = sum-limit (λ n → leg (f n))
  (λ n → reg-leg (sub n)) (λ n → ≤-trans (s≤s z≤) (≤-trans (step n) (inflation (f (suc n)))))

built-positive : ∀ {a} → Built a → hs hz ≤ᵛ a
built-positive one = ≤-refl _
built-positive {hl _} (repeat {a} p) = ≤l 1 (≤-trans (built-positive p) (≤⊞ a hz))
built-positive (limit p) = ≤l zero (built-positive (p zero))
assoc-same : ∀ (a b c : Cd) → Same ((a ⊞ b) ⊞ c) (a ⊞ (b ⊞ c))
assoc-same a b hz = refl-same (a ⊞ b)
  where
  refl-same : ∀ (a : Cd) → Same a a
  refl-same hz = zz
  refl-same (hs a) = ss (refl-same a)
  refl-same (hl f) = ll (λ n → refl-same (f n))
assoc-same a b (hs c) = ss (assoc-same a b c)
assoc-same a b (hl f) = ll (λ n → assoc-same a b (f n))

complete-prefix : ∀ {b} → Built b → ∀ a → Reg (leg a) → Reg (leg (a ⊞ b))
complete-prefix one a r = r
complete-prefix (limit {f} p) a r = sum-limit (λ n → leg (a ⊞ f n))
  (λ n → complete-prefix (p n) a r)
  (λ n → ≤-trans (built-positive (p (suc n)))
    (≤-trans (right-add a (f (suc n))) (inflation (a ⊞ f (suc n)))))
complete-prefix (repeat {a = b} p) a r = sum-limit (λ n → leg (a ⊞ leftMul b n))
  (λ n → terms n a r)
  (λ n → ≤-trans (built-positive p) (≤-trans (≤⊞ b (leftMul b n))
    (≤-trans (right-add a (leftMul b (suc n))) (inflation (a ⊞ leftMul b (suc n))))))
  where
  terms : ∀ n a → Reg (leg a) → Reg (leg (a ⊞ leftMul b n))
  terms zero a r = r
  terms (suc n) a r = reg-same (leg-same (assoc-same a b (leftMul b n)))
    (terms n (a ⊞ b) (complete-prefix p a r))

zero-add : ∀ (a : Cd) → Same (hz ⊞ a) a
zero-add hz = zz
zero-add (hs a) = ss (zero-add a)
zero-add (hl f) = ll (λ n → zero-add (f n))
complete-built : ∀ {a} → Built a → Reg (leg a)
complete-built {a} p = reg-same (leg-same (zero-add a)) (complete-prefix p hz tt)
```
