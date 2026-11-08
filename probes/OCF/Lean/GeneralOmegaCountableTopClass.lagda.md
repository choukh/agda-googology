# 原分类路径的逐点坐标重建

只归纳cl生成的路径；并层的原分量编号保持不变。函数坐标只证
逐点往返，不拼接为函数等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableTopClass where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf

data Back {B κ} : C.Cl {S⊥} B κ → Set where
  restored : ∀ {i p to} (eq : C.along p ≡ κ) →
    (∀ e → to (C.frA p e) ≡ subst (E (F B)) eq e) → Back (C.nw i p to)
cl-back : ∀ B κ → Back (C.cl B κ)
cl-back hz ()
cl-back (hs B) (inj₁ κ) with C.cl B κ | cl-back B κ
... | C.nw i p to | restored refl r = restored refl r
cl-back (hs B) (inj₂ _) = restored refl (λ e → refl)
cl-back (hl f) (n , κ) with C.cl (f n) κ | cl-back (f n) κ
... | C.nw i p to | restored refl r = restored refl r
cl-back (hΩ () f) κ

pick-self : ∀ {B i} (lB : LgB B) (p : hs i ⊲ B) {A : Set} (to : HB (F i) → A) →
  C.pick S⊥ to (hsuc p) (cmpB (hsuc p) (hsuc hself) _ lB) ≡
  C.keep (C.along p) (λ e → to (C.frA p e))
pick-self lB hself to = refl
pick-self lB (hsuc p) to = refl
pick-self lB (hlim n p) to = refl
pick-self lB (hLim {κ = ()} b p) to

data Returns (B : Cd) (κ : K (F B)) : C.Dc F (hs B) B (E (F B) κ) → Set where
  returned : (fr : E (F B) κ → E (F B) κ) → (∀ e → fr e ≡ e) →
    Returns B κ (C.keep κ fr)
class-old : ∀ B lB κ → Returns B κ (classify (hs B) lB B (hsuc hself) (inj₁ κ))
class-old B lB κ with C.cl B κ | cl-back B κ
... | C.nw i p to | restored refl r rewrite pick-self lB p to = returned (λ e → to (C.frA p e)) r
```
