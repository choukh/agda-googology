# 实际第二次Γ调用的全部有限高度路径

这里只证明原树的第一位置；不从值比较反推路径，也不假设Γ单调。
原stage 1的首分量经过两次完成，仍保留任意有限高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableCapturePath where
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (stage)

add-num : ∀ m n → num m ⊞ num n ≡ num (n + m)
add-num m zero = refl
add-num m (suc n) rewrite add-num m n = refl
leg-num : ∀ n → leg (num n) ≡ num n
leg-num zero = refl
leg-num (suc n) rewrite leg-num n = refl
ones : ∀ n → leftMul (hs hz) n ≡ num n
ones zero = refl
ones (suc n) rewrite ones n | add-num 1 n | N.+-comm n 1 = refl

sum : (ℕ → ℕ) → ℕ → ℕ
sum f zero = f zero
sum f (suc n) = f (suc n) + sum f n
sum-num : ∀ f n → Σ₀ (λ j → num (f j)) n ≡ num (sum f n)
sum-num f zero = refl
sum-num f (suc n) rewrite sum-num f n | add-num (sum f n) (f (suc n)) = refl
sum-leg-num : ∀ f n → Σ₀ (λ j → leg (num (f j))) n ≡ num (sum f n)
sum-leg-num f zero = leg-num (f zero)
sum-leg-num f (suc n) rewrite sum-leg-num f n | leg-num (f (suc n))
  | add-num (sum f n) (f (suc n)) = refl

num-path′ : ∀ {m n} → m ≤′ n → num m ⊲ num n
num-path′ ≤′-refl = hself
num-path′ (≤′-step p) = hsuc (num-path′ p)
num-path : ∀ {m n} → m ≤ n → num m ⊲ num n
num-path p = num-path′ (N.≤⇒≤′ p)

sum-large : ∀ f n → f n ≤ sum f n
sum-large f zero = N.≤-refl
sum-large f (suc n) = N.m≤m+n _ _

first-sum : ∀ n → Σ₀ (λ j → leg (leftMul (hs hz) j)) n ≡ num (sum (λ j → j) n)
first-sum zero = refl
first-sum (suc n) rewrite first-sum n | ones (suc n) | leg-num n
  | add-num (sum (λ j → j) n) n = refl
second-sum : ∀ n → Σ₀ (λ j → leg (Σ₀ (λ i → leg (leftMul (hs hz) i)) j)) n
  ≡ num (sum (sum (λ j → j)) n)
second-sum zero = refl
second-sum (suc n) rewrite second-sum n | first-sum (suc n)
  | leg-num (n + sum (λ j → j) n)
  | add-num (sum (sum (λ j → j)) n) (n + sum (λ j → j) n) = refl

finite-in-height : ∀ n → num n ⊲ leg (stage 1)
finite-in-height n = hlim 0 (hlim n branch)
  where
  branch : num n ⊲ Σ₀ (λ j → leg (Σ₀ (λ i → leg (leftMul (hs hz) i)) j)) n
  branch rewrite second-sum n = num-path
    (N.≤-trans (sum-large (λ j → j) n) (sum-large (sum (λ j → j)) n))
```
