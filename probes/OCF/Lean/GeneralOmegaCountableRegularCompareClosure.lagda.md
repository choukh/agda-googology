# 有向模拟的原地板及完成闭包

右侧极限只凭实际项进入累计完成；不使用一般值序穿过leg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareClosure where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.CountableCompletionRun using (item-sum)

right-add : ∀ {B b c} → Sim B b c → ∀ a → Sim B b (a ⊞ c)
right-add sz a = sz
right-add (ss p) a = ss (right-add p a)
right-add (sr p) a = sr (right-add p a)
right-add (sl p) a = sl (λ n → right-add (p n) a)
right-add (sli n p) a = sli n (right-add p a)
right-add (so p) a = so (λ r → right-add (p r) a)
right-add (sor p) a = sor (λ e → right-add (p e) a)
add : ∀ {B a b c d} → Sim B a b → Sim B c d → Sim B (a ⊞ c) (b ⊞ d)
add {d = d} p sz = prefix p d
  where
  prefix : ∀ {B a b} → Sim B a b → ∀ c → Sim B a (b ⊞ c)
  prefix p hz = p
  prefix p (hs c) = sr (prefix p c)
  prefix p (hl f) = sli zero (prefix p (f zero))
  prefix p (hΩ κ f) = sor (λ e → prefix p (f e))
add p (ss q) = ss (add p q)
add p (sr q) = sr (add p q)
add p (sl q) = sl (λ n → add p (q n))
add p (sli n q) = sli n (add p q)
add p (so q) = so (λ r → add p (q r))
add p (sor q) = sor (λ e → add p (q e))
up-sim : ∀ {B a b} → Sim B a b → Sim (hs B) (up a) (up b)
up-sim sz = sz
up-sim (ss p) = ss (up-sim p)
up-sim (sr p) = sr (up-sim p)
up-sim (sl p) = sl (λ n → up-sim (p n))
up-sim (sli n p) = sli n (up-sim p)
up-sim (so p) = so (λ r → up-sim (p r))
up-sim (sor p) = sor (λ e → up-sim (p e))
iota-sim : ∀ {f : ℕ → Cd} {n a b} → Sim (f n) a b → Sim (hl f) (ι n a) (ι n b)
iota-sim sz = sz
iota-sim (ss p) = ss (iota-sim p)
iota-sim (sr p) = sr (iota-sim p)
iota-sim (sl p) = sl (λ n → iota-sim (p n))
iota-sim (sli n p) = sli n (iota-sim p)
iota-sim (so p) = so (λ r → iota-sim (p r))
iota-sim (sor p) = sor (λ e → iota-sim (p e))
floor-self : ∀ B → Sim B (floor B) (floor B)
sums-self : ∀ f n → Sim (hl f) (C.ΣT S⊥ (hs hz) f n) (C.ΣT S⊥ (hs hz) f n)
floor-self hz = ss sz
floor-self (hs B) = so up-sim
floor-self (hl f) = sl (sums-self f)
floor-self (hΩ () f)
sums-self f zero = iota-sim (floor-self (f zero))
sums-self f (suc n) = add (sums-self f n) (iota-sim (floor-self (f (suc n))))
left-sim : ∀ {B a b} → Sim B a b → ∀ n → Sim B (leftMul a n) (leftMul b n)
left-sim p zero = sz
left-sim p (suc n) = add p (left-sim p n)
iterate-sim : ∀ {B} {f g : HB (F B) → HB (F B)} →
  (∀ {a b} → Sim B a b → Sim B (f a) (g b)) →
  ∀ {a b} → Sim B a b → ∀ n → Sim B (iterate f a n) (iterate g b n)
iterate-sim fg p zero = p
iterate-sim fg p (suc n) = fg (iterate-sim fg p n)

sum-value : ∀ f g → (∀ n → f n ≤ᵛ g n) → ∀ n → Σ₀ f n ≤ᵛ Σ₀ g n
sum-value f g p zero = p zero
sum-value f g p (suc n) = ≤-trans (⊞-≤ˡ (sum-value f g p n) _) (⊞-≤ʳ _ (p (suc n)))
complete : ∀ {a b} → Sim hz a b → leg a ≤ᵛ leg b
complete sz = z≤
complete (ss p) = s≤s (complete p)
complete (sr p) = ≤s (complete p)
complete (sl {f} {g} p) = l≤ (λ n → ≤l n (sum-value (λ i → leg (f i)) (λ i → leg (g i)) (λ i → complete (p i)) n))
complete (sli {f = f} n p) = ≤l n (≤-trans (complete p) (item-sum (λ i → leg (f i)) n))
complete (so {κ = ()} p)
complete (sor {κ = ()} p)
```
