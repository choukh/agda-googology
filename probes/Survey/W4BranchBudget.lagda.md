# 首座正塔的完整分支签名需要任意长的下降

第四层，无条件。在首座正塔的分支类型里能找到任意有限长度的嵌套。按一次取分支就减一的办法，整座塔没有自然数预算。定理量化于签名允许的位置，实际选中的操作另论。

```agda
{-# OPTIONS --safe --without-K #-}
module Survey.W4BranchBudget where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; n≤1+n; 1+n≰n)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
import W4Block as W

data Chain : W.L → ℕ → Set where
  stop : ∀ {a} → Chain a zero
  branch : ∀ {a n} (p : W.Pos a) → Chain (W.at a p) n → Chain a (suc n)

numeral : ℕ → W.Tr W.zero
numeral zero = W.zero
numeral (suc n) = W.suc (numeral n)

level : ℕ → W.L
level n = W.zero W.⊕ W.↑ W.zero (numeral n)

full-length : ∀ n → Chain (level n) n
full-length zero = stop
full-length (suc n) = branch (inj₂ (tt , inj₁ tt)) (full-length n)

tower-length : ∀ n → Chain (W.tw 1) (suc n)
tower-length n = branch (inj₂ (numeral n , inj₁ tt)) (full-length n)

Bound : W.L → ℕ → Set
Bound a k = ∀ n → Chain a n → n ≤ k

level-bound : ∀ k → Bound (level k) k
level-bound zero .zero stop = z≤n
level-bound (suc k) .zero stop = z≤n
level-bound (suc k) (suc n) (branch (inj₂ (tt , inj₁ tt)) tail) = s≤s (level-bound k n tail)
level-bound (suc k) (suc n) (branch (inj₂ (tt , inj₂ p)) tail) =
  ≤-trans (level-bound k (suc n) (branch p tail)) (n≤1+n k)

unbounded : ∀ k → Bound (W.tw 1) k → ⊥
unbounded k cap = 1+n≰n (cap (suc k) (tower-length k))
```
