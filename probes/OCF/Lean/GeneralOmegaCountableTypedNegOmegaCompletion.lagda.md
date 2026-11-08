# 正则输入完成后的遗传第2项界

每个内部ℕ节点的第2项至少为3。这是完成后的结构约束，不是输入值
的上界；标准ω的第2项为2，因而不能作为这种完成树的位置同形出现。
只使用Reg，不假定任意完成树都满足此性质。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableTypedNegOmegaCompletion where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; omega; omega-legal)
open import OCF.Lean.CountableCompletionRun using (right-add; inflation)
open import OCF.Lean.FrozenWorldLift using (Same; ll; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

SecondThree : Cd → Set
SecondThree hz = ⊤
SecondThree (hs a) = SecondThree a
SecondThree (hl f) = (num 3 ≤ᵛ f 2) × (∀ n → SecondThree (f n))
SecondThree (hΩ () f)

add-three : ∀ {a b} → SecondThree a → SecondThree b → SecondThree (a ⊞ b)
add-three {b = hz} pa pb = pa
add-three {b = hs b} pa pb = add-three pa pb
add-three {a} {hl f} pa (bound , sub) =
  ≤-trans bound (right-add a (f 2)) , (λ n → add-three pa (sub n))
add-three {b = hΩ () f} pa pb

sum-three : ∀ f → (∀ n → SecondThree (f n)) → ∀ n → SecondThree (Σ₀ f n)
sum-three f p zero = p zero
sum-three f p (suc n) = add-three (sum-three f p n) (p (suc n))

second-budget : ∀ f → Reg (hl f) → num 3 ≤ᵛ Σ₀ (λ n → leg (f n)) 2
second-budget f (step , sub) = ≤-trans
  (⊞-≤ˡ one (num 2)) (⊞-≤ʳ (Σ₀ (λ n → leg (f n)) 1) two)
  where
  one-raw : num 1 ≤ᵛ f 1
  one-raw = ≤-trans (s≤s z≤) (step 0)
  one : num 1 ≤ᵛ Σ₀ (λ n → leg (f n)) 1
  one = ≤-trans one-raw (≤-trans (inflation (f 1)) (right-add (leg (f 0)) (leg (f 1))))
  two : num 2 ≤ᵛ leg (f 2)
  two = ≤-trans (s≤s one-raw) (≤-trans (step 1) (inflation (f 2)))

completed-three : ∀ {a} → Reg a → SecondThree (leg a)
completed-three {a = hz} p = tt
completed-three {a = hs a} p = completed-three p
completed-three {a = hl f} p = second-budget f p , sum-three (λ n → leg (f n))
  (λ n → completed-three (proj₂ p n))
completed-three {a = hΩ () f} p

position-three : ∀ {a b : Cd} → a ⊲ b → SecondThree b → SecondThree a
position-three hself p = p
position-three (hsuc q) p = position-three q p
position-three (hlim n q) p = position-three q (proj₂ p n)
position-three (hLim {κ = ()} e q) p

no-omega-shape : ∀ {a} → SecondThree a → Same omega a → ⊥
no-omega-shape p (ll q) = ¬s≤ᵛ (num 2)
  (≤-trans (proj₁ p) (same-value (same-sym (q 2))))
no-completed-omega-position : ∀ {a b} → Reg a → b ⊲ leg a → Same omega b → ⊥
no-completed-omega-position reg pos shape = no-omega-shape
  (position-three pos (completed-three reg)) shape

regular-num : ∀ n → Reg (num n)
regular-num zero = tt
regular-num (suc n) = regular-num n
regular-omega : Reg omega
regular-omega = (λ n → ≤-refl _) , regular-num
omega-instance : SecondThree (leg omega)
omega-instance = completed-three regular-omega
```

零、所有有限数及合法的非有限ω均给Reg实例，性质并非矛盾前提。
结论只排原位置中与标准ω同形的树；尚未在此把旧前驱关系反射成
这种位置，也没有否定任何ψΩ值比较或Γ路线。
