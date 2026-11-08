# 旧种类跨一次source上移的实际决定

右侧保留两次raise，逐Class处理；不把两条公共界路径判相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceDecision where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision

up-class : ∀ m {c B B′ A} (cl : Class c A) → FiniteClass cl →
  (lB : LgB B) (lB′ : LgB B′)
  (pc : c ⊲ B) (pc′ : hs c ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′) →
  SameDecision (decide pt lB (raise pc cl))
    (decide pt′ lB′ (raise pc′ (raise (hsuc hself) cl)))
up-class m (base κ to fr a b) fc lB lB′ pc pc′ pt pt′ = kept _ _
up-class m (rank i pi to fr a b) (n , refl) lB lB′ pc pc′ pt pt′ =
  actual-rank n m lB lB′ (⊲ᴮ-tr pi pc)
    (⊲ᴮ-tr (⊲ᴮ-tr pi (hsuc hself)) pc′) pt pt′ to

up-component : ∀ n m κ {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : hs (num n) ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′) →
  SameDecision (decide pt lB (raise pc (classify (num n) κ)))
    (decide pt′ lB′ (raise pc′ (raise (hsuc hself) (classify (num n) κ))))
up-component n m κ = up-class m (classify (num n) κ) (finite-classify n κ)
```
