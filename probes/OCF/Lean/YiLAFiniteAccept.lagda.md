# 正有限目标的保留判定与经典参照
> 编译定理，条件（排中律），验收侧。对每个正有限目标、每个零层孩子的后继顶槽位，`agrees` 双向传递保留证据。构造性算法见 `YiLAFiniteKeep`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLAFiniteAccept where
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
open import OCF.Lean.YiLAFiniteKeep

module _ (lem : LEM) where
  open Sharp lem
  law : ∀ ℓ o p j oj → (Kept (kp♯ ℓ o p j oj) → at ℓ p ≺ᴸ j) × (at ℓ p ≺ᴸ j → Kept (kp♯ ℓ o p j oj))
  law ℓ o p j oj with Dk j (at ℓ p)
  ... | inj₁ le = (λ ()) , (λ lt → ≺-irrefl _ (≺≼ j (at ℓ p) lt le))
  ... | inj₂ lt with slot♯ j (at ℓ p) lt
  ...   | q , e , e′ = (λ _ → lt) , (λ _ → tt)

  sharp-kept : ∀ n c → Set
  sharp-kept n c = Kept (kp♯ (child (suc c)) (proj₂ (Ok-tw 1) (suc c)) (top c) (target n) (proj₂ (Ok-tw 1) (suc (fin n))))

  agrees : ∀ n c → (Kept (keep n c) → sharp-kept n c) × (sharp-kept n c → Kept (keep n c))
  agrees n c with law (child (suc c)) (proj₂ (Ok-tw 1) (suc c)) (top c) (target n) (proj₂ (Ok-tw 1) (suc (fin n)))
  ... | to , back = (λ k → back (sound n c k)) , (λ k → complete n c (to k))
```
