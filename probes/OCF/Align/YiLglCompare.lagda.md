# D7 接口检验：严格步进仍支持带公共界的比较

以平行 LF／Legalˢ 搭建最小 Level 与 Position，并平移原 compare 的证明。
Level.lim 的参数现在必须提供 Properˢ；不能再用弱 CP 填这个位置。
判定对象仍须带同一合法界里的 CP 位置，不是在所有裸层号上比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglCompare where

open import Data.Nat.Base using (ℕ; suc; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.YiLglCore as F
open import OCF.Align.YiLglVal using (CP; CP-tr)
import OCF.Align.YiLglVal as V
open import OCF.Align.YiLglStrict using (Properˢ; Legalˢ; weak; Ω-legalˢ; tw-proper; tower-legalˢ; Λ-legalˢ)

record Level : Set where
  constructor level
  field tree : F.LF
        legal : Legalˢ tree
open Level public

Ω : Level → Level
Ω x = level (V.Ω̂ (tree x)) (Ω-legalˢ (tree x) (legal x))

lim : (f : ℕ → Level) → (∀ n → Properˢ (tree (f n)) (tree (f (suc n)))) → Level
lim f step = level (F.lim (λ n → tree (f n))) (step , (λ n → legal (f n)))

tower : ℕ → Level
tower n = level (V.tw n) (tower-legalˢ n)

Λ : Level
Λ = level V.Λ Λ-legalˢ

record Position (bound : Level) : Set where
  constructor located
  field part : Level
        place : CP (tree part) (tree bound)
open Position public

steps : ∀ {f : ℕ → F.LF} → (∀ n → CP (f n) (f (suc n))) →
  ∀ {n m} → n <′ m → CP (f n) (f m)
steps step ≤′-refl = step _
steps step (≤′-step p) = CP-tr (steps step p) (step _)

compare : ∀ {a b} (bound : F.LF) → CP a bound → CP b bound → Legalˢ bound → CP a b ⊎ CP b a
compare bound V.self q lawful = inj₂ q
compare bound p V.self lawful = inj₁ p
compare (F.suc bound) (V.suc p) (V.suc q) lawful = compare bound p q lawful
compare (F.lim f) (V.lim n p) (V.lim m q) (step , lawful) with <-cmp n m
... | tri< n<m _ _ = compare (f m) (CP-tr p (steps (λ n → weak (step n)) (<⇒<′ n<m))) q (lawful m)
... | tri> _ _ m<n = compare (f n) p (CP-tr q (steps (λ n → weak (step n)) (<⇒<′ m<n))) (lawful n)
... | tri≈ _ refl _ = compare (f n) p q (lawful n)
compare (F.lc k c t g) (V.fst p) (V.fst q) (lk , first , mono , same , lt , lg) = compare t p q lt

data Order (a b : F.LF) : Set where
  below : Properˢ a b → Order a b
  equal : a ≡ b → Order a b
  above : Properˢ b a → Order a b

from-left : ∀ {a b} → CP a b → Order a b
from-left V.self = equal refl
from-left (V.suc p) = below (OCF.Align.YiLglStrict.under-suc p)
from-left (V.lim n p) = below (OCF.Align.YiLglStrict.under-lim n p)
from-left (V.fst p) = below (OCF.Align.YiLglStrict.under-first p)

from-right : ∀ {a b} → CP b a → Order a b
from-right V.self = equal refl
from-right (V.suc p) = above (OCF.Align.YiLglStrict.under-suc p)
from-right (V.lim n p) = above (OCF.Align.YiLglStrict.under-lim n p)
from-right (V.fst p) = above (OCF.Align.YiLglStrict.under-first p)

bounded-compare : ∀ (bound : Level) (a b : Position bound) → Order (tree (part a)) (tree (part b))
bounded-compare bound (located a p) (located b q) with compare (tree bound) p q (legal bound)
... | inj₁ ab = from-left ab
... | inj₂ ba = from-right ba
```

只在 ℕ 上判定分支编号，结构严格步进只是携带证据；保留 CP 的自反性和比较的相等结果。
本篇没有平移 InvD 或 all-retained-reg，不将这些旧类型上的结论自动搬到新 LF。
