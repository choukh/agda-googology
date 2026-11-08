# 同一有限分量中的实际比较

保留实际source component的路径，不把不同Pos证明当作相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedMixedLegalClass where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (<-cmp; <-irrefl; ≡-irrelevant)
open import Data.Sum using (inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedMixedLegalIf
import OCF.Lean.BoundedContextClosed as C

column : ∀ n {a b} (p : a ⊲[ C.w ] up (C.num n)) (q : b ⊲[ C.w ] up (C.num n)) →
  cmpB (hLim {κ = inj₂ tt} {g = up} (hlim n hself) p) (hLim {κ = inj₂ tt} {g = up} (hlim n hself) q) C.legal-w C.legal-B ≡
  cmpB p q C.legal-w (proj₂ C.legal-B C.legal-w (hlim n hself))
column n p q with <-cmp n n
... | tri< bad _ _ = ⊥-elim (<-irrefl refl bad)
... | tri> _ _ bad = ⊥-elim (<-irrefl refl bad)
... | tri≈ _ eq _ rewrite ≡-irrelevant eq refl = refl
```
