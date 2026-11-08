# 原fold跨source上移的全有限逻辑同余

实际消费有限决定规范化与二元坐标运输。same/above直接比较原diagonal
的全部反馈链，不将Same当函数相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceRun where
open import Data.Nat using (suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (decide; keep; same; above)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteRunCoord
open import OCF.Align.BoundedCompletionFinitePlaceIf
open import OCF.Align.BoundedCompletionFinitePlaceDecision
import OCF.Lean.BoundedDiagonalRel as D

coherent-up : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : num (suc n) ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  {a b} → Rel (num n) a b →
  Rel (num m) (at n m lB pc pt a) (at (suc n) m lB′ pc′ pt′ (up b))
coherent-up n m lB lB′ pc pc′ pt pt′ rz = rs rz
coherent-up n m lB lB′ pc pc′ pt pt′ (rs r) =
  rel-repeat (coherent-up n m lB lB′ pc pc′ pt pt′ r)
coherent-up n m lB lB′ pc pc′ pt pt′ (rl r) =
  rl (λ j → coherent-up n m lB lB′ pc pc′ pt pt′ (r j))
coherent-up n m lB lB′ pc pc′ pt pt′ (ro {κ = κ} {f = f} {g = g} r)
  with decide pt lB (raise pc (classify (num n) κ))
     | decide pt′ lB′ (raise pc′ (raise (hsuc hself) (classify (num n) κ)))
     | up-component n m κ lB lB′ pc pc′ pt pt′
     | decide-allowed (Coord (num n) κ) pt lB (raise pc (classify (num n) κ))
         (raise-supported (Coord (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
     | decide-finite pt lB (raise pc (classify (num n) κ))
         (finite-raise pc (classify (num n) κ) (finite-classify n κ))
... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin =
  ro (λ x y xy → coherent-up n m lB lB′ pc pc′ pt pt′ (r (fr x) (fr y) (al x y xy)))
... | same to | .(same to) | same-rank .to | al | fin =
  D.Sim.result (Rel (num m)) (Rel (num m))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at (suc n) m lB′ pc′ pt′ (up (g (to e))))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at (suc n) m lB′ pc′ pt′ (up (g (to e))))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → coherent-up n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))
    (λ {x} {y} xy → coherent-up n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))
... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl =
  D.Sim.result (Rel (num j)) (Rel (num m))
    (λ e → at n j lB pc (⊲ᴮ-tr (hsuc hself) pi) (f (to e)))
    (λ e → at (suc n) j lB′ pc′ (⊲ᴮ-tr (hsuc hself) pi′) (up (g (to e))))
    (λ e → at n m lB pc pt (f (to e)))
    (λ e → at (suc n) m lB′ pc′ pt′ (up (g (to e))))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → coherent-up n j lB lB′ pc pc′
      (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′) (r (to x) (to y) (al x y xy)))
    (λ {x} {y} xy → coherent-up n m lB lB′ pc pc′ pt pt′ (r (to x) (to y) (al x y xy)))

instance-bridge : PlacementBridge
instance-bridge = record { coherent-up = coherent-up }
```
