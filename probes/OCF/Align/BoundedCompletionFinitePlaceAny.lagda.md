# 原单组件路径逐节点变化的同余

处理原PH-⊞引入的PH-mono路径，不把路径函数相等当作前提。
仍是同一原placed树上的证书，每个Ω事件各自调用已证实际决定规范化。
以下复制前轮证明形状以泛化Path参数；未复制或改写运行器定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceAny where
open import Data.Nat using (suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldIf using (Path)
open import OCF.Align.BoundedNativeFoldRun using (decide; keep; same; above)
import OCF.Align.BoundedNativeFoldRun as R
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteRunCoord
open import OCF.Align.BoundedCompletionFinitePlaceDecision
import OCF.Lean.BoundedDiagonalRel as D

atAny : ∀ n m {B} → LgB B → num m ⊲ B →
  (a : HB (Native (num n))) → Path B (placed (num n) a) → HB (Native (num m))
atAny n m {B} lB pt a pa = R.fold B lB (num m) pt (placed (num n) a) pa

any-same : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  {a b} → Rel (num n) a b →
  (pa : Path B (placed (num n) a)) →
  (pb : Path B′ (placed (num n) b)) →
  Rel (num m) (atAny n m lB pt a pa)
    (atAny n m lB′ pt′ b pb)
any-same n m lB lB′ pt pt′ rz pa pb = rs rz
any-same n m lB lB′ pt pt′ (rs r) pa pb =
  rel-repeat (any-same n m lB lB′ pt pt′ r pa pb)
any-same n m lB lB′ pt pt′ (rl r) pa pb =
  rl (λ j → any-same n m lB lB′ pt pt′ (r j) (pa j) (pb j))
any-same n m lB lB′ pt pt′ (ro {κ = κ} {f = f} {g = g} r) (pc , pg) (pc′ , pg′)
  with decide pt lB (raise pc (classify (num n) κ))
     | decide pt′ lB′ (raise pc′ (classify (num n) κ))
     | actual-component n m κ lB lB′ pc pc′ pt pt′
     | decide-allowed (Coord (num n) κ) pt lB (raise pc (classify (num n) κ))
         (raise-supported (Coord (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
     | decide-finite pt lB (raise pc (classify (num n) κ))
         (finite-raise pc (classify (num n) κ) (finite-classify n κ))
... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin =
  ro (λ x y xy → any-same n m lB lB′ pt pt′ (r (fr x) (fr y) (al x y xy)) (pg (fr x) tt) (pg′ (fr y) tt))
... | same to | .(same to) | same-rank .to | al | fin =
  D.Sim.result (Rel (num m)) (Rel (num m))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny n m lB′ pt′ (g (to e)) (pg′ (to e) tt))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny n m lB′ pt′ (g (to e)) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → any-same n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → any-same n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl =
  D.Sim.result (Rel (num j)) (Rel (num m))
    (λ e → atAny n j lB (⊲ᴮ-tr (hsuc hself) pi) (f (to e)) (pg (to e) tt))
    (λ e → atAny n j lB′ (⊲ᴮ-tr (hsuc hself) pi′) (g (to e)) (pg′ (to e) tt))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny n m lB′ pt′ (g (to e)) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → any-same n j lB lB′
      (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′) (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → any-same n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))


any-up : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  {a b} → Rel (num n) a b →
  (pa : Path B (placed (num n) a)) →
  (pb : Path B′ (placed (num (suc n)) (up b))) →
  Rel (num m) (atAny n m lB pt a pa)
    (atAny (suc n) m lB′ pt′ (up b) pb)
any-up n m lB lB′ pt pt′ rz pa pb = rs rz
any-up n m lB lB′ pt pt′ (rs r) pa pb =
  rel-repeat (any-up n m lB lB′ pt pt′ r pa pb)
any-up n m lB lB′ pt pt′ (rl r) pa pb =
  rl (λ j → any-up n m lB lB′ pt pt′ (r j) (pa j) (pb j))
any-up n m lB lB′ pt pt′ (ro {κ = κ} {f = f} {g = g} r) (pc , pg) (pc′ , pg′)
  with decide pt lB (raise pc (classify (num n) κ))
     | decide pt′ lB′ (raise pc′ (raise (hsuc hself) (classify (num n) κ)))
     | up-component n m κ lB lB′ pc pc′ pt pt′
     | decide-allowed (Coord (num n) κ) pt lB (raise pc (classify (num n) κ))
         (raise-supported (Coord (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
     | decide-finite pt lB (raise pc (classify (num n) κ))
         (finite-raise pc (classify (num n) κ) (finite-classify n κ))
... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin =
  ro (λ x y xy → any-up n m lB lB′ pt pt′ (r (fr x) (fr y) (al x y xy)) (pg (fr x) tt) (pg′ (fr y) tt))
... | same to | .(same to) | same-rank .to | al | fin =
  D.Sim.result (Rel (num m)) (Rel (num m))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny (suc n) m lB′ pt′ (up (g (to e))) (pg′ (to e) tt))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny (suc n) m lB′ pt′ (up (g (to e))) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → any-up n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → any-up n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl =
  D.Sim.result (Rel (num j)) (Rel (num m))
    (λ e → atAny n j lB (⊲ᴮ-tr (hsuc hself) pi) (f (to e)) (pg (to e) tt))
    (λ e → atAny (suc n) j lB′ (⊲ᴮ-tr (hsuc hself) pi′) (up (g (to e))) (pg′ (to e) tt))
    (λ e → atAny n m lB pt (f (to e)) (pg (to e) tt))
    (λ e → atAny (suc n) m lB′ pt′ (up (g (to e))) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → any-up n j lB lB′
      (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′) (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → any-up n m lB lB′ pt pt′ (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))

```
