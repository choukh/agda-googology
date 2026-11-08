# 原θ全有限混合族的单组件归并

左边始终是原N.θ及它的实际source类型。model只是右侧用于比较的
单组件前缀模型；没有用它替换原输入或原路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceTheta where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeFoldRun as R
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFinitePlaceAny
open import OCF.Align.BoundedCompletionFinitePlaceAppend
open import OCF.Align.BoundedCompletionFinitePlacePER

model : ∀ n → HB (Native (num n))
model zero = hz ⊞ floor zero
model (suc n) = up (model n) ⊞ floor (suc n)

model-rel : ∀ n → Rel (num n) (model n) (model n)
model-rel zero = rel-add rz (floor-rel zero)
model-rel (suc n) = rel-add (up-rel (num n) (model-rel n)) (floor-rel (suc n))

lower-path : ∀ n {B} (a : HB (Native (num n))) →
  Path B (placed (num (suc n)) (up a)) → Path B (placed (num n) a)
lower-path n hz p = tt
lower-path n (hs a) p = lower-path n a p
lower-path n (hl f) p = λ j → lower-path n (f j) (p j)
lower-path n (hΩ κ g) (pc , pg) =
  ⊲ᴮ-tr (hsuc hself) pc , (λ e ad → lower-path n (g e) (pg e tt))

theta-rel : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  (pa : Path B (N.θ (num (suc n))))
  (pb : Path B′ (placed (num n) (model n))) →
  Rel (num m) (R.fold B lB (num m) pt (N.θ (num (suc n))) pa)
    (atAny n m lB′ pt′ (model n) pb)
theta-rel zero m lB lB′ pt pt′ pa pb =
  append-place zero m lB lB′ pt pt′ hz hz
    (λ j q q′ p p′ → rs rz) (floor-rel zero) pa pb
theta-rel (suc n) m lB lB′ pt pt′ pa pb =
  append-place (suc n) m lB lB′ pt pt′ (N.θ (num (suc n))) (up (model n))
    prefix (floor-rel (suc n)) pa pb
  where
  prefix : PrefixRel (suc n) lB lB′ (N.θ (num (suc n))) (up (model n))
  prefix j q q′ p p′ = rel-trans (num j)
    (theta-rel n j lB lB′ q q′ p (lower-path n (model n) p′))
    (any-up n j lB′ lB′ q′ q′ (model-rel n) (lower-path n (model n) p′) p′)

normal : ∀ n → HB (Native hz)
normal n = at n zero (legal-num n) hself (z⊲ᴮ (num n)) (model n)

theta-normal : ∀ n {B} (lB : LgB B) (pt : hz ⊲ B)
  (pa : Path B (N.θ (num (suc n)))) →
  Rel hz (R.fold B lB hz pt (N.θ (num (suc n))) pa) (normal n)
theta-normal n lB pt pa = theta-rel n zero lB (legal-num n) pt (z⊲ᴮ (num n)) pa
  (N.component-path (num n) (num n) hself (model n))

known-height : ∀ e n → e ≡ num (suc n) → ∀ {B} (lB : LgB B) (pt : hz ⊲ B)
  (pa : Path B (N.θ e)) → Rel hz (R.fold B lB hz pt (N.θ e) pa) (normal n)
known-height .(num (suc n)) n refl lB pt pa = theta-normal n lB pt pa
```

全n证明覆盖原θ的全部有限累加分量，并接受原θ-path（也接受PH-⊞内部
改变过的路径）。没有把混合分支限制为只返回原分量。
normal仍用原R.fold；与Old有限塔参照的值比较尚未由本篇给出。
