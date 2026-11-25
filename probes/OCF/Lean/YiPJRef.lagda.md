# 有限读回层号的参考相邻路径
验收文件；编译定理。实际路径仅给数字界，另造参考路径；没有断言实际路径等于规范路径。
Reference 的 Rref/canRef 只用于复用与路径无关的 Mω、GBω；实际折叠仍用原 R。
来源：YiPJPath.bound 与 YiCLLow.Sb；不改树、折叠、合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJRef where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth)
open import OCF.Lean.YiLRBridge using (τ₂)
open import OCF.Lean.YiPJPath using (bound)

raise : ∀ {n j} → Sb n j → Sb (suc n) (suc j)
raise s0 = s0
raise (ss s) = ss (raise s)
fromLe : ∀ n j → j ≤ⁿ n → Sb n j
fromLe zero zero z≤n = s0
fromLe (suc n) zero z≤n = ss (fromLe n zero z≤n)
fromLe (suc n) (suc j) (s≤s p) = raise (fromLe n j p)

toP : ∀ A ℓ → ℓ ≡ fn A → ∀ B ℓ′ → ℓ′ ≡ fn B → Sb B A → ℓ ≤ ℓ′
toP A _ refl B _ refl s = pth s
sound : ∀ A ℓ (e : ℓ ≡ fn A) B ℓ′ (e′ : ℓ′ ≡ fn B) (s : Sb B A)
      → τ₂ e e′ (toP A ℓ e B ℓ′ e′ s) ≡ pth s
sound A _ refl B _ refl s = refl

module Reference (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : ∀ n → G n ≤ G (suc n)) where
  sibling : ∀ n → Sb (d (suc n)) (d n)
  sibling n = fromLe (d (suc n)) (d n) (bound (d (suc n)) (G (suc n)) (eG (suc n)) (d n) (G n) (eG n) (R n))
  Rref : ∀ n → G n ≤ G (suc n)
  Rref n = toP (d n) (G n) (eG n) (d (suc n)) (G (suc n)) (eG (suc n)) (sibling n)
  canRef : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (Rref n) ≡ pth s
  canRef n = sibling n , sound (d n) (G n) (eG n) (d (suc n)) (G (suc n)) (eG (suc n)) (sibling n)
```
