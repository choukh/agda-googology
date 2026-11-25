# 带等式的有限路径
验收文件；编译定理。源、目标层号均抽象并带等式，任意实际路径给出数字高度界。
self 以两端高度等式换型，inc/inu 对路径递归；不把路径读成字面 Sb。
这不是关系保持或完整 Q；入口为后续 YiPJCase。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJPath where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst₂)
open import OCF.Lean.YiRWOps using (c₀)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn)

height : L → ℕ
height zero = zero
height (nd s h) = suc (height (h (c₀ s)))
height-fn : ∀ n → height (fn n) ≡ n
height-fn zero = refl
height-fn (suc n) = cong suc (height-fn n)
rank-e : ∀ {n} (ℓ : L) → ℓ ≡ fn n → height ℓ ≡ n
rank-e {n} ℓ e = trans (cong height e) (height-fn n)

bound : (N : ℕ) (ℓ : L) → ℓ ≡ fn N → (j : ℕ) (j′ : L) → j′ ≡ fn j → j′ ≤ ℓ → j ≤ⁿ N
bound N ℓ e j .ℓ e′ self = subst₂ _≤ⁿ_ (rank-e ℓ e′) (rank-e ℓ e) ≤-refl
bound zero (nd s h) () j j′ e′ v
bound (suc N) (nd sL h) () j j′ e′ v
bound (suc N) (nd (sΩ k) h) () j j′ e′ v
bound (suc N) _ refl j j′ e′ (inc tt v) = m≤n⇒m≤1+n (bound N _ refl j j′ e′ v)
bound (suc N) _ refl j j′ e′ (inu vs) = m≤n⇒m≤1+n (bound N _ refl j j′ e′ (vs tt))

self-test : 2 ≤ⁿ 2
self-test = bound 2 (fn 2) refl 2 (fn 2) refl self
inc-test : 1 ≤ⁿ 2
inc-test = bound 2 (fn 2) refl 1 (fn 1) refl (inc tt self)
inu-test : 1 ≤ⁿ 2
inu-test = bound 2 (fn 2) refl 1 (fn 1) refl (inu (λ _ → self))
```
