# 内部View、值一致与结构消去

本篇的同类型部分是Object，不仅是外部read输出。每个View的值与对象
值逐字相等；对象递归沿原树的字面子树，未假定任意View关系良基。
泛型KS的E未必是低层树，具体LH实例的坐标合法性另篇验证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewRun where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.HigherIndexViewIf

module View (S : KS) (w : Wd S) (lw : LgW S w) where
  open Domain S w lw public
  position : ∀ {a b} → a ⊲[ w ] b → restrict a ⊲[ tt ] restrict b
  position hself = hself
  position (hsuc p) = hsuc (position p)
  position (hlim n p) = hlim n (position p)
  position (hLim {c = c} bd p) = hLim {c = c , bd} tt (position p)

  legal : ∀ a → LgB a → LgB (restrict a)
  legal hz l = tt
  legal (hs a) l = legal a l
  legal (hl f) (st , l) = (λ n → position (st n)) , λ n → legal (f n) (l n)
  legal (hΩ κ g) (mo , l) =
    (λ {c = e} {c′ = d} _ _ _ p → position (mo lw (proj₂ e) (proj₂ d) p)) ,
    (λ {c = e} _ _ → legal (g (proj₁ e)) (l lw (proj₂ e)))

  data Shape : Set where
    zero : Shape
    successor : Object → Shape
    limit : (f : ℕ → Object) → (∀ n → value (f n) ⊲[ tt ] value (f (suc n))) → Shape
    omega : (κ : K S) → (g : E Target κ → Object) →
      (∀ e d → Pr Target κ tt e d → value (g e) ⊲[ tt ] value (g d)) → Shape

  assemble : Shape → HB Target
  assemble zero = hz
  assemble (successor a) = hs (value a)
  assemble (limit f st) = hl (λ n → value (f n))
  assemble (omega κ g mo) = hΩ κ (λ e → value (g e))

  view : Object → Shape
  view (hz , l) = zero
  view (hs a , l) = successor (a , l)
  view (hl f , st , l) = limit (λ n → f n , l n) (λ n → position (st n))
  view (hΩ κ g , mo , l) = omega κ (λ e → g (proj₁ e) , l lw (proj₂ e))
    (λ e d p → position (mo lw (proj₂ e) (proj₂ d) p))

  value-view : ∀ x → value x ≡ assemble (view x)
  value-view (hz , l) = refl
  value-view (hs a , l) = refl
  value-view (hl f , l) = refl
  value-view (hΩ κ g , l) = refl

  both-values : ∀ x → (value x ≤ᵛ assemble (view x)) × (assemble (view x) ≤ᵛ value x)
  both-values x rewrite value-view x = ≤-refl _ , ≤-refl _

  rec : ∀ {A : Set} → A → (A → A) → ((ℕ → A) → A) →
    ((κ : K S) → (E Target κ → A) → A) → Object → A
  rec z s l o = go
    where
    go : Object → _
    go (hz , p) = z
    go (hs a , p) = s (go (a , p))
    go (hl f , st , p) = l (λ n → go (f n , p n))
    go (hΩ κ g , mo , p) = o κ (λ e → go (g (proj₁ e) , p lw (proj₂ e)))
```
