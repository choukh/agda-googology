# 原正则位置的完成高度也未必有字面共同界

反例原高度的首支为1，随后为ω、ω+1、ω+2……；a取第1支ω。
原高度合法且Reg，a也合法且Reg。完成后的leg ω首支为0，而
完成大高度的每个内部ℕ节点首支都为正。遗传形状据此排除位置，
再由同界Sim定向定理排除任何合法字面公共上界。

这只否定CompletionBoundIf的全域补界字段，不否定Height.capture、
Γ右吸收或整个路线；后几者并未要求该字段对所有原位置存在。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableCompletionBoundNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; omega; omega-legal)
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg)
open import OCF.Lean.GeneralOmegaCountableCapturePath using (sum; sum-leg-num)
open import OCF.Lean.GeneralOmegaCountableSimCompletion using (from-position)
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (sim-to-position)
open import OCF.Lean.GeneralOmegaCountableCompletionBoundIf
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

-- 每个内部极限的第0分量为正；沿任何字面位置遗传。
FirstPositive : Cd → Set
FirstPositive hz = ⊤
FirstPositive (hs a) = FirstPositive a
FirstPositive (hl f) = (hs hz ≤ᵛ f zero) × (∀ n → FirstPositive (f n))
FirstPositive (hΩ () f)
position-first : ∀ {a b : Cd} → a ⊲ b → FirstPositive b → FirstPositive a
position-first hself p = p
position-first (hsuc q) p = position-first q p
position-first (hlim n q) p = position-first q (proj₂ p n)
position-first (hLim {κ = ()} e q) p

finite-tail : ∀ a → FirstPositive a → ∀ n → FirstPositive (a ⊞ num n)
finite-tail a p zero = p
finite-tail a p (suc n) = finite-tail a p n
plus-completed-omega : ∀ a → FirstPositive a → hs hz ≤ᵛ a → FirstPositive (a ⊞ leg omega)
plus-completed-omega a p positive = positive , branch
  where
  branch : ∀ n → FirstPositive (a ⊞ Σ₀ (λ k → leg (num k)) n)
  branch n rewrite sum-leg-num (λ k → k) n = finite-tail a p (sum (λ k → k) n)
plus-omega-tail : ∀ n a → FirstPositive a → hs hz ≤ᵛ a →
  FirstPositive (a ⊞ leg (omega ⊞ num n))
plus-omega-tail zero a p positive = plus-completed-omega a p positive
plus-omega-tail (suc n) a p positive = plus-omega-tail n a p positive

branches : ℕ → Cd
branches zero = hs hz
branches (suc n) = omega ⊞ num n
B : Cd
B = hl branches
B-legal : LgB B
B-legal = legal-step , sub
  where
  legal-step : ∀ n → branches n ⊲ branches (suc n)
  legal-step zero = hlim 1 hself
  legal-step (suc n) = hsuc hself
  sub : ∀ n → LgB (branches n)
  sub zero = tt
  sub (suc zero) = omega-legal
  sub (suc (suc n)) = sub (suc n)
source-position : omega ⊲ B
source-position = hlim 1 hself

num-regular : ∀ n → Reg (num n)
num-regular zero = tt
num-regular (suc n) = num-regular n
omega-regular : Reg omega
omega-regular = (λ n → ≤-refl _) , num-regular
tail-regular : ∀ n → Reg (omega ⊞ num n)
tail-regular zero = omega-regular
tail-regular (suc n) = tail-regular n
B-regular : Reg B
B-regular = regular-step , sub
  where
  regular-step : ∀ n → hs (branches n) ≤ᵛ branches (suc n)
  regular-step zero = ≤l 2 (≤-refl _)
  regular-step (suc n) = ≤-refl _
  sub : ∀ n → Reg (branches n)
  sub zero = tt
  sub (suc n) = tail-regular n

sums : ℕ → Cd
sums = Σ₀ (λ n → leg (branches n))
sums-positive : ∀ n → hs hz ≤ᵛ sums n
sums-positive zero = ≤-refl _
sums-positive (suc n) = ≤-trans (sums-positive n) (≤⊞ (sums n) (leg (branches (suc n))))
sums-first : ∀ n → FirstPositive (sums n)
sums-first zero = tt
sums-first (suc n) = plus-omega-tail n (sums n) (sums-first n) (sums-positive n)
completed-first : FirstPositive (leg B)
completed-first = sums-positive zero , sums-first
omega-not-first : FirstPositive (leg omega) → ⊥
omega-not-first p = ¬s≤ᵛ hz (proj₁ p)
no-completed-position : leg omega ⊲ leg B → ⊥
no-completed-position p = omega-not-first (position-first p completed-first)

no-common : Common (leg omega) (leg B) → ⊥
no-common (W , lW , pa , pb) = no-completed-position
  (sim-to-position lW pa pb (from-position source-position))
no-completion-bounding : PositionCompletionBounding → ⊥
no-completion-bounding m = no-common (PositionCompletionBounding.bound m B-legal source-position)
no-regular-completion-bounding :
  (∀ {a C : Cd} → LgB C → Reg a → Reg C → a ⊲ C → Common (leg a) (leg C)) → ⊥
no-regular-completion-bounding bound = no-common
  (bound B-legal omega-regular B-regular source-position)
```

所有输入前提均由B-legal、B-regular、omega-legal、omega-regular和
source-position实际提供。结论没有要求裸下标判等或全局比较；恰好
相反，它说明共同合法界在原完成机制中不能凭Sim证据自动补出。
