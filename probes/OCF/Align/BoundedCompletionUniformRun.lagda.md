# 原单组件fold的全有限层有向比较

实际消费有限决定规范化与二元坐标运输。same/above直接比较原diagonal
的全部反馈链，不将Same当函数相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformRun where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (decide; keep; same; above)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionUniformClosure
open import OCF.Align.BoundedCompletionUniformCoord
import OCF.Lean.BoundedDiagonalRel as D

positive : ∀ n m {B} (lB : LgB B) (pc : num n ⊲ B) (pt : num m ⊲ B)
  (a : HB (Native (num n))) → Value (num m) (hs hz) (at n m lB pc pt a)
positive n m lB pc pt hz = vs vz
positive n m lB pc pt (hs a) = vli 0 (positive n m lB pc pt a)
positive n m lB pc pt (hl f) = vli 0 (positive n m lB pc pt (f 0))
positive n m lB pc pt (hΩ κ g) with decide pt lB (raise pc (classify (num n) κ))
... | keep κ′ fr = vor (λ c → positive n m lB pc pt (g (fr c)))
... | same to = vli 0 (positive n m lB pc pt (g (to (hs hz))))
... | above i pi q to = vli 0 (positive n m lB pc pt (g (to (hs hz))))

compare : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  {a b} → Value (num n) a b →
  Value (num m) (at n m lB pc pt a) (at n m lB′ pc′ pt′ b)
compare n m lB lB′ pc pc′ pt pt′ {b = b} vz = positive n m lB′ pc′ pt′ b
compare n m lB lB′ pc pc′ pt pt′ (vs r) =
  repeat-rel (compare n m lB lB′ pc pc′ pt pt′ r)
compare n m lB lB′ pc pc′ pt pt′ (vr r) =
  vli 0 (compare n m lB lB′ pc pc′ pt pt′ r)
compare n m lB lB′ pc pc′ pt pt′ (vl r) =
  vl (λ j → compare n m lB lB′ pc pc′ pt pt′ (r j))
compare n m lB lB′ pc pc′ pt pt′ (vli j r) =
  vli j (compare n m lB lB′ pc pc′ pt pt′ r)
compare n m lB lB′ pc pc′ pt pt′ (vo {κ = κ} {f = f} {g = g} r)
  with decide pt lB (raise pc (classify (num n) κ))
     | decide pt′ lB′ (raise pc′ (classify (num n) κ))
     | actual-component n m κ lB lB′ pc pc′ pt pt′
     | decide-allowed (CoordValue (num n) κ) pt lB (raise pc (classify (num n) κ))
         (raise-supported (CoordValue (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
     | decide-finite pt lB (raise pc (classify (num n) κ))
         (finite-raise pc (classify (num n) κ) (finite-classify n κ))
... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin =
  vo (λ x y xy → compare n m lB lB′ pc pc′ pt pt′ (r (fr x) (fr y) (al x y xy)))
... | same to | .(same to) | same-rank .to | al | fin =
  D.Sim.result (Value (num m)) (Value (num m))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at n m lB′ pc′ pt′ (g (to e)))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at n m lB′ pc′ pt′ (g (to e)))
    (vs vz) add-rel add-rel (λ p → vl (λ n → vli n (p n)))
    (λ {x} {y} xy → compare n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))
    (λ {x} {y} xy → compare n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))
... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl =
  D.Sim.result (Value (num j)) (Value (num m))
    (λ e → at n j lB pc (⊲ᴮ-tr (hsuc hself) pi) (f (to e)))
    (λ e → at n j lB′ pc′ (⊲ᴮ-tr (hsuc hself) pi′) (g (to e)))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at n m lB′ pc′ pt′ (g (to e)))
    (vs vz) add-rel add-rel (λ p → vl (λ n → vli n (p n)))
    (λ {x} {y} xy → compare n j lB lB′ pc pc′
      (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′) (r (to x) (to y) (al x y xy)))
    (λ {x} {y} xy → compare n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))

compare n m lB lB′ pc pc′ pt pt′ (vor {κ = κ} {g = g} p)
  with decide pt′ lB′ (raise pc′ (classify (num n) κ))
... | keep κ′ fr = vor (λ c → compare n m lB lB′ pc pc′ pt pt′ (p (fr c)))
... | same to = vli 0 (compare n m lB lB′ pc pc′ pt pt′ (p (to (hs hz))))
... | above i pi q to = vli 0 (compare n m lB lB′ pc pc′ pt pt′ (p (to (hs hz))))

instance-bridge : NativeComparison
instance-bridge = record { compare = compare }
```
