# YiLean 验收：派发的有限测试

**验收文件，档位：有限测试 (`refl` 的计算核对，不是一般定理)。** 公共上界 ω+2 上目标在根 (层号 ω+1)、结点在下一格 (层号 ω) 时保留，槽位是根；
ω 上两个不同分支的位置 (层号 3 与 1) 搬到同一支后比较，保留；同层号与更高层号折叠。派发完全性的一般定理没有写。折叠在 [YiLeanFold](YiLeanFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanAccTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; lv)

fin : ℕ → R
fin zero = G.zero
fin (suc n) = G.suc (fin n)

ω : R
ω = G.lim fin

fin-lgl : ∀ n → Lgl zero (fin n)
fin-lgl zero = tt
fin-lgl (suc n) = fin-lgl n

ω-lgl : Lgl zero ω
ω-lgl = (λ n → inj₂ (inj₁ refl)) , fin-lgl

Vω+2 : Lv (up zero (G.suc (G.suc ω)))
Vω+2 = lv (G.suc (G.suc ω)) ω-lgl

keep-ω : cmp Vω+2 (inj₁ tt) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl
keep-ω = refl

fold-same : cmp Vω+2 (inj₁ tt) (inj₁ tt) ≡ fold
fold-same = refl

fold-above : cmp Vω+2 (inj₂ (inj₁ tt)) (inj₁ tt) ≡ fold
fold-above = refl

cross : cmp (lv ω ω-lgl) (4 , inj₁ tt) (2 , inj₁ tt) ≡ keep (inj₂ (inj₁ tt)) refl
cross = refl
```
