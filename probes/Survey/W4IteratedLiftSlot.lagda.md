# 捕获上一整座标准塔后留下的实际正槽

第四层。首个正分支按第零孩子下行，留下的正槽是独立重置值的累加。每个被加项都含一个标准正块。给出槽本身属于该结构类的证书，再接回原标准塔的共同零槽预算。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftSlot where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import B12Terminal as T
import B20Room as Room
import B20OldBlocks as Short
import B21TowerPorts as Port
import Survey.W4TowerLawStandard as Standard
import Survey.W4IteratedLiftBlock as B
open T.Run

series : ∀ (g : ℕ → O.Tr⁺ W.zero) → B.Positive (proj₁ (O.limc⁺ (λ n → O.Ωt B.k O.⊞ g n)))
series g = B.collect prefix where
  seq = λ n → proj₁ (O.Ωt B.k O.⊞ g n)
  prefix : ∀ n → B.Positive (O.cum seq n)
  prefix zero = B.append B.seed (proj₁ (g 0))
  prefix (suc n) = B.join (prefix n) (B.append B.seed (proj₁ (g (suc n))))

Family = ℕ → O.Tr⁺ W.zero
tree : Family → B.Tr
tree g = proj₁ (O.limc⁺ (λ n → O.Ωt B.k O.⊞ g n))

data Series : B.Tr → Set where
  witness : ∀ g → Series (tree g)
positive : ∀ {t} → Series t → B.Positive t
positive (witness g) = series g

module Form (m : ℕ) where
  lo = W.tw m
  mid = W.tw (suc m)
  module Seq = Port.At m (F.B₀ mid) (O.Ωt W.zero)
  g = λ n → Seq.independent (Seq.index n)
  form : ∀ o → o ≡ P.Ok-tw (suc m) → ∀ b → b ≡ F.B₀ mid → ∀ c → c ≡ proj₁ (O.Ωt mid) → (u : B.k W.≤ lo) →
    Series (proj₁ (F.ψ mid o b B.k (W.inc W.zero u) (b B.k (W.inc W.zero u)) c))
  form _ refl _ refl _ refl u = witness g
```
