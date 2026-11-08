# 两个真实分类器在全部数值公共界上的匹配

验收辅助，共用冻结CountableFiniteIf。所有比较只沿同一个数值
公共界；先保留原cl给出的实际along/逆坐标，再证明提高源界时
原pick与原有限raise相容。目标路径仅在num n下用已证唯一性规范。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteClass where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaCountableObserveIf as C
import OCF.Lean.GeneralOmegaFiniteObserveIf as F
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Lean.GeneralOmegaCountableNumber using (path-unique)
open import OCF.Align.GeneralOmegaCountableFiniteRel
open import OCF.Align.GeneralOmegaCountableFiniteIf

Restored : ∀ {n κ κ′} → Kind n κ κ′ → C.C.Cl {S⊥} (num n) κ → Set
Restored k (C.C.bas () to)
Restored {n} {κ} {κ′} k (C.C.nw r pr to) =
  Σ (Kind n (C.C.along pr) κ′) (λ k′ →
    ∀ {a b} → Coord n k′ a b → Coord n k (to (C.C.frA pr a)) b)

restore : ∀ {n κ κ′} (k : Kind n κ κ′) → Restored k (C.C.cl (num n) κ)
restore high = high , (λ r → r)
restore {n = suc n} (low {κ = κ} k) with C.C.cl (num n) κ | restore k
... | C.C.bas () to | r
... | C.C.nw i pi to | k′ , r = low k′ , r

self-pick : ∀ {B i A} (to : HB (C.F i) → A) (pi : hs i ⊲ B) (lB : LgB B) →
  C.C.pick S⊥ to pi (cmpB pi hself tt lB) ≡
  C.C.keep (C.C.along pi) (λ c → to (C.C.frA pi c))
self-pick to hself lB = refl
self-pick to (hsuc p) lB = refl
self-pick to (hlim n p) lB = refl
self-pick to (hLim {κ = ()} b p) lB

self-match : ∀ {n κ κ′} (k : Kind n κ κ′) →
  Match F.here hself (Coord n k)
    (C.classify (num n) (num-legal n) (num n) hself κ) (F.keep κ′ (λ e → e))
self-match {n} {κ} k with C.C.cl (num n) κ | restore k
... | C.C.bas () to | r
... | C.C.nw i pi to | k′ , r = subst
  (λ d → Match F.here hself (Coord n k) d (F.keep _ (λ e → e)))
  (sym (self-pick to pi (num-legal n))) (kept k′ r)

lift-decision : ∀ {B t A} → C.C.Dc C.F B t A → C.C.Dc C.F (hs B) t A
lift-decision (C.C.keep κ fr) = C.C.keep κ fr
lift-decision (C.C.same to) = C.C.same to
lift-decision (C.C.above i pi ti to) = C.C.above i (hsuc pi) ti to

lift-pick : ∀ {B t i A} (to : HB (C.F i) → A) (pi : hs i ⊲ B)
  (r : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  lift-decision (C.C.pick S⊥ to pi r) ≡ C.C.pick S⊥ to (hsuc pi) r
lift-pick to pi (inj₂ p) = refl
lift-pick to pi (inj₁ hself) = refl
lift-pick to pi (inj₁ (hsuc hself)) = refl
lift-pick to pi (inj₁ (hsuc (hsuc p))) = refl
lift-pick to pi (inj₁ (hsuc (hlim n p))) = refl
lift-pick to pi (inj₁ (hsuc (hLim {κ = ()} b p)))

lift-classify : ∀ n m (pt : num m ⊲ num n) κ →
  C.classify (num (suc n)) (num-legal (suc n)) (num m) (hsuc pt) (inj₁ κ) ≡
  lift-decision (C.classify (num n) (num-legal n) (num m) pt κ)
lift-classify n m pt κ with C.C.cl (num n) κ
... | C.C.bas () to
... | C.C.nw i pi to = sym (lift-pick to pi (cmpB pi pt tt (num-legal n)))

lift-match : ∀ {n m A A′} {p : F.Within n m} {pt : num m ⊲ num n}
  {Q : A → A′ → Set} {d v} → Match p pt Q d v →
  Match (F.lower p) (hsuc pt) Q (lift-decision d) (F.raise v)
lift-match (kept k r) = kept k r
lift-match (same r) = same r
lift-match (above r) = above r

path : ∀ {n m} → F.Within n m → num m ⊲ num n
path F.here = hself
path (F.lower p) = hsuc (path p)

canonical-match : ∀ {n m κ κ′} (p : F.Within n m) (k : Kind n κ κ′) →
  Match p (path p) (Coord n k)
    (C.classify (num n) (num-legal n) (num m) (path p) κ) (F.view p κ′)
canonical-match F.here k = self-match k
canonical-match {suc n} {m} {inj₁ κ} (F.lower p) (low k) = subst
  (λ d → Match (F.lower p) (hsuc (path p)) (Coord n k) d (F.raise (F.view p _)))
  (sym (lift-classify n m (path p) κ)) (lift-match (canonical-match p k))
canonical-match (F.lower F.here) high = same (λ r → r)
canonical-match (F.lower (F.lower p)) high = above (λ r → r)

matched : ∀ {n m κ κ′} (p : F.Within n m) (pt : num m ⊲ num n) (k : Kind n κ κ′) →
  Match p pt (Coord n k)
    (C.classify (num n) (num-legal n) (num m) pt κ) (F.view p κ′)
matched {n} p pt k rewrite path-unique n pt (path p) = canonical-match p k

instance-classification : Classification
instance-classification = record { matched = matched }
```

instance-classification实填全部n、目标及kind。kept始终保留原along
返回的拷贝，same与above保持原分类器的真实反馈层及路径，没有
将整个共同高度上的任意raw树当成自相关。
