# 原有限classify在self-target处重建种类与坐标

证明实际SelfKeep实例；只用沿后继的Ctx运输，不引入函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueRebuild where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueKeep
open import OCF.Align.BoundedCompletionAlongSuccessor

key : ∀ {c A} → Class c A → K (Native c)
key {c} (base κ to fr a b) = base-kind c κ
key (rank i pi to fr a b) = along pi
back : ∀ {c A} (cl : Class c A) → E (Native c) (key cl) → A
back {c} (base κ to fr a b) e = to (base-fr c κ e)
back (rank i pi to fr a b) e = to (fr-along pi e)

Recovery : ∀ c κ → Class c (E (Native c) κ) → Set
Recovery c κ cl = Σ (key cl ≡ κ)
  (λ eq → ∀ e → back cl e ≡ subst (E (Native c)) eq e)

subst-compose : ∀ {A : Set} (P : A → Set) {x y z} (p : x ≡ y) (q : y ≡ z) e →
  subst P (trans p q) e ≡ subst P q (subst P p e)
subst-compose P refl refl e = refl
subst-old : ∀ {S : KS} {κ κ′ : K S} (p : κ ≡ κ′) e →
  subst (E (step S)) (cong inj₁ p) e ≡ subst (E S) p e
subst-old refl e = refl

raise-recovery : ∀ c κ (cl : Class c (E (Native c) κ)) → Recovery c κ cl →
  Recovery (hs c) (inj₁ κ) (raise (hsuc hself) cl)
raise-recovery c κ (base κ₀ to fr a b) (eq , h) =
  cong inj₁ eq , λ e → trans (h e) (sym (subst-old eq e))
raise-recovery c κ (rank i pi to fr a b) (eq , h) =
  trans (along-suc pi) (cong inj₁ eq) , λ e →
    trans (cong to (fr-suc pi e))
      (trans (h (subst (E (Native (hs c))) (along-suc pi) e))
        (trans (sym (subst-old eq (subst (E (Native (hs c))) (along-suc pi) e)))
          (sym (subst-compose (E (Native (hs c))) (along-suc pi) (cong inj₁ eq) e))))

recover : ∀ n κ → Recovery (num n) κ (classify (num n) κ)
recover zero κ = refl , λ e → refl
recover (suc n) (inj₁ κ) = raise-recovery (num n) κ (classify (num n) κ) (recover n κ)
recover (suc n) (inj₂ _) = refl , λ e → refl

self-compute : ∀ {c A} (lc : LgB c) (cl : Class c A) →
  decide {B = c} {t = c} hself lc cl ≡ keep (key cl) (back cl)
self-compute lc (base κ to fr a b) = refl
self-compute lc (rank i hself to fr a b) = refl
self-compute lc (rank i (hsuc p) to fr a b) = refl
self-compute lc (rank i (hlim n p) to fr a b) = refl

raise-self : ∀ {c A} (cl : Class c A) → raise hself cl ≡ cl
raise-self (base κ to fr a b) = refl
raise-self (rank i pi to fr a b) = refl

keeps-transfer : ∀ {B n κ κ′} (f : E (Native (num n)) κ′ → E (Native (num n)) κ)
  (eq : κ′ ≡ κ) → (∀ e → f e ≡ subst (E (Native (num n))) eq e) →
  Keeps {B} {n} κ (keep κ′ f)
keeps-transfer f refl h = retained f h

self-keep : ∀ n κ → Keeps {B = num n} {n = n} κ
  (decide {B = num n} {t = num n} hself (legal-num n) (raise hself (classify (num n) κ)))
self-keep n κ with recover n κ
... | eq , h = subst (Keeps {B = num n} {n = n} κ)
  (sym (trans (cong (decide hself (legal-num n)) (raise-self (classify (num n) κ)))
    (self-compute (legal-num n) (classify (num n) κ))))
  (keeps-transfer (back (classify (num n) κ)) eq h)

instance-self : SelfKeep
instance-self = record { self-keep = self-keep }
```
