# 合法树的有界第一位置比较

定理的每次比较都有同一棵合法原树作公共上界。只用位置证明、
ℕ 分支的相邻第一位置和树的合法性，不比较裸层号，不读记号码。
输出给真第一位置或原树相等；不要求 Level 中的合法性证据相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLevelCompare where

open import Data.Nat.Base using (ℕ; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP; Legal; CP-tr)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiLevelBase

steps : ∀ {f : ℕ → LF} →
  (∀ n → CP (f n) (f (Data.Nat.Base.suc n))) →
  ∀ {n m} → n <′ m → CP (f n) (f m)
steps step ≤′-refl = step _
steps step (≤′-step p) = CP-tr (steps step p) (step _)

compare : ∀ {a b} (bound : LF) → CP a bound → CP b bound → Legal bound → CP a b ⊎ CP b a
compare bound V.self q lawful = inj₂ q
compare bound p V.self lawful = inj₁ p
compare (F.suc bound) (V.suc p) (V.suc q) lawful = compare bound p q lawful
compare (F.lim f) (V.lim n p) (V.lim m q) (step , lawful) with <-cmp n m
... | tri< n<m _ _ = compare (f m) (CP-tr p (steps step (<⇒<′ n<m))) q (lawful m)
... | tri> _ _ m<n = compare (f n) p (CP-tr q (steps step (<⇒<′ m<n))) (lawful n)
... | tri≈ _ refl _ = compare (f n) p q (lawful n)
compare (F.lc k c t g) (V.fst p) (V.fst q) (lk , first , mono , same , lt , lg) = compare t p q lt

from-left : ∀ {a b} → CP a b → Order a b
from-left V.self = equal refl
from-left (V.suc p) = below (under-suc p)
from-left (V.lim n p) = below (under-lim n p)
from-left (V.fst p) = below (under-first p)

from-right : ∀ {a b} → CP b a → Order a b
from-right V.self = equal refl
from-right (V.suc p) = above (under-suc p)
from-right (V.lim n p) = above (under-lim n p)
from-right (V.fst p) = above (under-first p)

bounded-compare : ∀ (bound : Level) (a b : Position bound) →
  Order (tree (part a)) (tree (part b))
bounded-compare bound (located a p) (located b q) with compare (tree bound) p q (legal bound)
... | inj₁ ab = from-left ab
... | inj₂ ba = from-right ba
```

ℕ 比较只比较同一极限的分支编号；每次递归的公共上界下降到一个实际子树。
本定理不生产缺少的 place 证据，也不把层号字段自动视为第一位置。
因此它不是完整 ψ 派发或全部 Ω 位置实现定理。
