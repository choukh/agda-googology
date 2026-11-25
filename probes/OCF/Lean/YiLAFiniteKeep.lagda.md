# 有限目标层上的整列保留
> 编译定理，无经典前提。塔第 1 项的后继孩子顶槽位对任意正有限目标可计算保留，返回实际槽位、分支转换与保零证明。
> `sound`、`complete` 给出与严格层值比较的两向蕴涵。量化所有零层孩子，目标的前驱取自然数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLAFiniteKeep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath using (_⊑_; self; inc; wk; psh; pshBr; pshFirst)
open import OCF.Lean.YiRWFold using (Keep)
open import OCF.Lean.YiRVLevel using (_≼ᴸ_; _≺ᴸ_; n≼; z≼; ≼≺; ≺-irrefl; ≼ᴸ-refl; up≼; ⊕-strictʳ; ↑-strict)

child : Tr zero → L
child c = zero ⊕ ↑ zero c

fin : ℕ → Tr zero
fin zero    = zero
fin (suc n) = suc (fin n)

data Within : ℕ → Tr zero → Set where
  same : ∀ {n} → Within n (fin n)
  prev : ∀ {n c} → Within n c → Within (suc n) c

at-zero : ∀ n → Within n zero
at-zero zero    = same
at-zero (suc n) = prev (at-zero n)

bump : ∀ {n c} → Within n c → Within (suc n) (suc c)
bump same     = same
bump (prev w) = prev (bump w)

path : ∀ {n c} → Within n c → child c ⊑ child (fin n)
path same     = self
path (prev w) = inc tt (path w)

bound : ∀ {n c} → Within n c → child c ≼ᴸ child (fin n)
bound same     = ≼ᴸ-refl _
bound (prev w) = up≼ tt (bound w)

-- 极限的第 n 个孩子已经达到第 n 层；只用树自带的相邻步进。
grows : (f : ℕ → Tr zero) → (∀ n → zero ⊢ f n ◃ f (suc n)) → ∀ n → child (fin n) ≼ᴸ child (f n)
grows f a zero    = z≼
grows f a (suc n) = n≼ (λ _ → ≼≺ (child (f (suc n))) (grows f a n)
  (⊕-strictʳ zero (↑ zero (f (suc n))) (↑-strict zero (a n))))

cut : (n : ℕ) (c : Tr zero) → Within n c ⊎ (child c ≼ᴸ child (fin n) → ⊥)
cut n zero = inj₁ (at-zero n)
cut zero (suc c) = inj₂ (λ { (n≼ k) → k tt })
cut (suc n) (suc c) with cut n c
... | inj₁ w = inj₁ (bump w)
... | inj₂ no = inj₂ (λ { (n≼ k) → no (proj₂ (k tt)) })
cut n (lim f a) = inj₂ (λ { (n≼ k) → ≺-irrefl (child (fin n)) (≼≺ (child (fin n)) (grows f a n) (k n)) })

target : ℕ → L
target n = child (fin (suc n))

top : ∀ c → Pos (child (suc c))
top c = inj₂ (tt , inj₁ tt)

keep : (n : ℕ) (c : Tr zero) → Keep (target n) (Br (child (suc c)) (top c)) zero
keep n c with cut n c
... | inj₂ _ = nothing
... | inj₁ w = just (inj₂ (tt , psh v (inj₁ tt)) , pshBr v (inj₁ tt) , pshFirst v (inj₁ tt))
  where v = wk (path w)

Kept : ∀ {A : Set} → Maybe A → Set
Kept nothing  = ⊥
Kept (just _) = ⊤

sound : ∀ n c → Kept (keep n c) → at (child (suc c)) (top c) ≺ᴸ target n
sound n c with cut n c
... | inj₁ w = λ _ → tt , bound w
... | inj₂ _ = λ ()

complete : ∀ n c → at (child (suc c)) (top c) ≺ᴸ target n → Kept (keep n c)
complete n c with cut n c
... | inj₁ _ = λ _ → tt
... | inj₂ no = λ lt → no (proj₂ lt)
```
