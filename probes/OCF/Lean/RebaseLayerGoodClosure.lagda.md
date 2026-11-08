# 递归采样域的地板与原生成闭包

Good的准入字段给出递归需要的低层树证书，所有有限原地板及原Whole
全轨道因此可实例化；不把仅顶层自证强行反演成递归证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodClosure where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.RebaseLayerIf using (vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerClosure using (add; repeat; act-mono)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Lean.RebaseCountableClosed as D

self : ∀ c {a} → Good c a → Value c a a
self c {a = hz} p = p
self c {a = hs a} p = proj₁ p
self c {a = hl f} p = proj₁ p
self c {a = hΩ κ g} p = proj₁ p

good-add : ∀ c {a b} → Good c a → Good c b → Good c (a ⊞ b)
good-add c {b = hz} ga gb = ga
good-add c {b = hs b} ga gb = add (self c ga) (self c gb) , good-add c ga (proj₂ gb)
good-add c {b = hl f} ga gb = add (self c ga) (self c gb) , (λ n → good-add c ga (proj₂ gb n))
good-add c {b = hΩ κ g} ga gb = add (self c ga) (self c gb) , (λ e se → good-add c ga (proj₂ gb e se))
good-mul : ∀ c {a} → Good c a → ∀ n → Good c (mul a n)
good-mul c ga zero = ga
good-mul c ga (suc n) = good-add c (good-mul c ga n) ga
good-act : ∀ c {a} → Good c a → Good c (act a)
good-act c {a = hz} ga = vs vz , vz
good-act c {a = hs a} ga = act-mono (self c {a = hs a} ga) , (λ n → good-mul c (good-act c (proj₂ ga)) n)
good-act c {a = hl f} ga = act-mono (self c {a = hl f} ga) , (λ n → good-act c (proj₂ ga n))
good-act c {a = hΩ κ g} ga = act-mono (self c ga) , (λ e se → good-act c (proj₂ ga e se))

pure-up : ∀ {a b} → a ≤ᵛ b → Value hz (up a) (up b)
pure-up z≤ = vz
pure-up (s≤s p) = vs (pure-up p)
pure-up (≤s p) = vr (pure-up p)
pure-up (l≤ p) = vl (λ n → pure-up (p n))
pure-up (≤l n p) = vli n (pure-up p)
good-pure : ∀ a → Good hz (up a)
good-pure hz = vz
good-pure (hs a) = pure-up (≤-refl (hs a)) , good-pure a
good-pure (hl f) = pure-up (≤-refl (hl f)) , (λ n → good-pure (f n))
up-value : ∀ c {a b} → Value c a b → Value (hs c) (up a) (up b)
up-value c vz = vz
up-value c (vs p) = vs (up-value c p)
up-value c (vr p) = vr (up-value c p)
up-value c (vl p) = vl (λ n → up-value c (p n))
up-value c (vli n p) = vli n (up-value c p)
up-value c (vo p) = vo (λ x y xy → up-value c (p x y xy))
up-value c (vor p) = vor (λ e se → up-value c (p e se))
good-up : ∀ c {a} → Good c a → Good (hs c) (up a)
good-up c {a = hz} ga = vz
good-up c {a = hs a} ga = up-value c (self c ga) , good-up c (proj₂ ga)
good-up c {a = hl f} ga = up-value c (self c ga) , (λ n → good-up c (proj₂ ga n))
good-up c {a = hΩ κ g} ga = up-value c (self c ga) , (λ e se → good-up c (proj₂ ga e se))

floor-good : ∀ n → Good (num n) (floor n)
floor-good zero = vo (λ x y xy → pure-up xy) , (λ e se → good-pure e)
floor-good (suc n) = vo (λ x y xy → up-value (num n) (proj₁ xy)) ,
  (λ e se → good-up (num n) se)
whole-good : ∀ n → Good (num 1) (Whole.Model.ce n)
whole-good zero = floor-good 1
whole-good (suc n) = good-add (num 1) (whole-good n) (good-act (num 1) (whole-good n))
D-good : ∀ n → Good (num 1) (D.levels n)
D-good zero = floor-good 1
D-good (suc n) = good-add (num 1) (D-good n) (good-act (num 1) (D-good n))
```

这些是真实非空实例。Good既不是原LgB的替代，也不单独说明下降输出
被C或EBO覆盖；下一义务是原at保持Good及有向关系。
