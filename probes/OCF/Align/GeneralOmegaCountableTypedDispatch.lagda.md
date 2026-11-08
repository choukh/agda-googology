# 原准入目标下的typed与native分派标签

验收专用。内部目标携hs t⊲B，kind秩携hs i⊲同一合法B；普通根零
目标不自动拥有这个字段，须另处理ψ⁰。这里只配对三种标签，不要求
旧比较的路径证明相等，也不省略keep/same两侧坐标的tr⁻运输。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedDispatch where
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (H; measure-position)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.GeneralOmegaCountableAdmittedOrder using (successor-in-bound)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; ≤l)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape; index-bound)

Cases : L.Ordᴵ → L.Ordᴵ → Set
Cases a b = (a L.≺ᴵ b) ⊎ ((b L.≺ᴵ a) ⊎ (a L.≅ᴵ b))
data Lower {a b} : Cases a b → Set where
  lower : ∀ p → Lower (inj₁ p)
data Upper {a b} : Cases a b → Set where
  upper : ∀ p → Upper (inj₂ (inj₁ p))
data Equal {a b} : Cases a b → Set where
  equal : ∀ e → Equal (inj₂ (inj₂ e))

lower-consistent : ∀ {a b} → a L.≺ᴵ b → (r : Cases a b) → Lower r
lower-consistent p (inj₁ q) = lower q
lower-consistent p (inj₂ (inj₁ q)) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-trans p q))
lower-consistent p (inj₂ (inj₂ e)) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respʳ p (L.≅ᴵ-sym e)))
upper-consistent : ∀ {a b} → b L.≺ᴵ a → (r : Cases a b) → Upper r
upper-consistent p (inj₁ q) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-trans q p))
upper-consistent p (inj₂ (inj₁ q)) = upper q
upper-consistent p (inj₂ (inj₂ e)) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respʳ p e))
equal-consistent : ∀ {a b} → a L.≅ᴵ b → (r : Cases a b) → Equal r
equal-consistent e (inj₁ p) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respʳ p (L.≅ᴵ-sym e)))
equal-consistent e (inj₂ (inj₁ p)) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respʳ p e))
equal-consistent e (inj₂ (inj₂ f)) = equal f

keep-order : ∀ {i t : Cd} li lt → hs i ⊲ t → height i li L.≺ᴵ height t lt
keep-order {i} li lt p = L.via
  (height-shape (same-refl i) li (lgB⊲ p tt lt)) (index-bound lt p)
above-order : ∀ {B t i : Cd} (lB : LgB B) (ht : hs t ⊲ B) (pi : hs i ⊲ B) →
  hs (H t) ≤ᵛ H i →
  height t (lgB⊲ ht tt lB) L.≺ᴵ height i (lgB⊲ pi tt lB)
above-order lB ht pi strict = keep-order (lgB⊲ ht tt lB) (lgB⊲ pi tt lB)
  (successor-in-bound lB ht (⊲ᴮ-tr (hsuc hself) pi) strict)

data Matched {B t A a b} (r : Cases a b) : C.Dc F B t A → Set where
  keep-tag : ∀ {κ fr} → Lower r → Matched r (C.keep κ fr)
  same-tag : ∀ {to} → Equal r → Matched r (C.same to)
  above-tag : ∀ {i pi pt to} → Upper r → Matched r (C.above i pi pt to)

pick-matched : ∀ {B t i : Cd} {A : Set} (lB : LgB B)
  (ht : hs t ⊲ B) (pi : hs i ⊲ B) (to : HB (F i) → A)
  (choice : (t ⊲ hs i) ⊎ (hs i ⊲ t))
  (r : Cases (height i (lgB⊲ pi tt lB)) (height t (lgB⊲ ht tt lB))) →
  Matched r (C.pick S⊥ to pi choice)
pick-matched lB ht pi to (inj₂ p) r = keep-tag
  (lower-consistent (keep-order (lgB⊲ pi tt lB) (lgB⊲ ht tt lB) p) r)
pick-matched {i = i} lB ht pi to (inj₁ hself) r = keep-tag
  (lower-consistent (keep-order {i = i} {t = hs i} (lgB⊲ pi tt lB) (lgB⊲ ht tt lB) hself) r)
pick-matched {i = i} lB ht pi to (inj₁ (hsuc hself)) r = same-tag
  (equal-consistent (height-shape (same-refl i) (lgB⊲ pi tt lB) (lgB⊲ ht tt lB)) r)
pick-matched lB ht pi to (inj₁ (hsuc (hsuc p))) r = above-tag
  (upper-consistent (above-order lB ht pi (s≤s (position-value (measure-position p)))) r)
pick-matched lB ht pi to (inj₁ (hsuc (hlim n p))) r = above-tag
  (upper-consistent (above-order lB ht pi (s≤s (≤l n (position-value (measure-position p))))) r)
pick-matched lB ht pi to (inj₁ (hsuc (hLim {κ = ()} e p))) r
```

该定理可消费原<ᴵ-dec的实际Cases结果，不将其替换成手选比较器。
所有严格旧层关系均从原同界准入路径翻译；本篇尚未给异合法证
Read运输、keep坐标完整相容或整个ψ观察定理。
