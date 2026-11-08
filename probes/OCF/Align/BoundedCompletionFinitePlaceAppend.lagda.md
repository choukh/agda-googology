# 原混合左前缀与单组件局部前缀的相容

PrefixRel是语义前缀引理的输入：前缀已在原fold下相关，右侧一个实际
组件中的Rel后缀可以同时追加。归纳仍在后缀结构，非假设整个和已相关。
任意Path参数吸收PH-⊞引入的PH-mono，不识别这些函数证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceAppend where
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
import OCF.Lean.BoundedDiagonalRel as D

left : ∀ n m {B} → LgB B → num m ⊲ B → (prefix : HB Source) →
  (a : HB (Native (num n))) → Path B (prefix ⊞ placed (num n) a) → HB (Native (num m))
left n m {B} lB pt prefix a pa = R.fold B lB (num m) pt (prefix ⊞ placed (num n) a) pa
right : ∀ n m {B} → LgB B → num m ⊲ B → (local a : HB (Native (num n))) →
  Path B (placed (num n) (local ⊞ a)) → HB (Native (num m))
right n m {B} lB pt local a pa = R.fold B lB (num m) pt (placed (num n) (local ⊞ a)) pa

PrefixRel : ∀ n {B B′} → LgB B → LgB B′ → HB Source → HB (Native (num n)) → Set
PrefixRel n {B} {B′} lB lB′ prefix local = ∀ m
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  (pa : Path B prefix) (pb : Path B′ (placed (num n) local)) →
  Rel (num m) (R.fold B lB (num m) pt prefix pa)
    (R.fold B′ lB′ (num m) pt′ (placed (num n) local) pb)

append-place : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  (prefix : HB Source) (local : HB (Native (num n))) →
  PrefixRel n lB lB′ prefix local →
  {a b : HB (Native (num n))} → Rel (num n) a b →
  (pa : Path B (prefix ⊞ placed (num n) a)) →
  (pb : Path B′ (placed (num n) (local ⊞ b))) →
  Rel (num m) (left n m lB pt prefix a pa)
    (right n m lB′ pt′ local b pb)
append-place n m lB lB′ pt pt′ prefix local H rz pa pb = H m pt pt′ pa pb
append-place n m lB lB′ pt pt′ prefix local H (rs r) pa pb =
  rel-repeat (append-place n m lB lB′ pt pt′ prefix local H r pa pb)
append-place n m lB lB′ pt pt′ prefix local H (rl r) pa pb =
  rl (λ j → append-place n m lB lB′ pt pt′ prefix local H (r j) (pa j) (pb j))
append-place n m lB lB′ pt pt′ prefix local H (ro {κ = κ} {f = f} {g = g} r) (pc , pg) (pc′ , pg′)
  with decide pt lB (raise pc (classify (num n) κ))
     | decide pt′ lB′ (raise pc′ (classify (num n) κ))
     | actual-component n m κ lB lB′ pc pc′ pt pt′
     | decide-allowed (Coord (num n) κ) pt lB (raise pc (classify (num n) κ))
         (raise-supported (Coord (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
     | decide-finite pt lB (raise pc (classify (num n) κ))
         (finite-raise pc (classify (num n) κ) (finite-classify n κ))
... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin =
  ro (λ x y xy → append-place n m lB lB′ pt pt′ prefix local H (r (fr x) (fr y) (al x y xy)) (pg (fr x) tt) (pg′ (fr y) tt))
... | same to | .(same to) | same-rank .to | al | fin =
  D.Sim.result (Rel (num m)) (Rel (num m))
    (λ e → left n m lB pt prefix (f (to e)) (pg (to e) tt))
    (λ e → right n m lB′ pt′ local (g (to e)) (pg′ (to e) tt))
    (λ e → left n m lB pt prefix (f (to e)) (pg (to e) tt))
    (λ e → right n m lB′ pt′ local (g (to e)) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → append-place n m lB lB′ pt pt′ prefix local H (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → append-place n m lB lB′ pt pt′ prefix local H (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl =
  D.Sim.result (Rel (num j)) (Rel (num m))
    (λ e → left n j lB (⊲ᴮ-tr (hsuc hself) pi) prefix (f (to e)) (pg (to e) tt))
    (λ e → right n j lB′ (⊲ᴮ-tr (hsuc hself) pi′) local (g (to e)) (pg′ (to e) tt))
    (λ e → left n m lB pt prefix (f (to e)) (pg (to e) tt))
    (λ e → right n m lB′ pt′ local (g (to e)) (pg′ (to e) tt))
    (rs rz) rel-add rel-add rl
    (λ {x} {y} xy → append-place n j lB lB′
      (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′) prefix local H (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))
    (λ {x} {y} xy → append-place n m lB lB′ pt pt′ prefix local H (r (to x) (to y) (al x y xy)) (pg (to x) tt) (pg′ (to y) tt))

```
