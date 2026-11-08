# 同一数值高度下的实际路径

只对字面有限高度num n证明路径唯一；不把它扩成一般Cd高度的
证明无关性，也不比较不同极限副本。另给完成及两份有限塔的类型
等式，供新可数观察器与原有限观察器核对同一源输入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableNumber where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symˡ)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
import OCF.Lean.GeneralOmegaFiniteObserveIf as Finite
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

-- 只判定是否等于给定数值树，不判定两棵任意Cd树相等。
pred : Cd → Cd
pred hz = hz
pred (hs a) = a
pred (hl f) = hz
pred (hΩ () f)
dec-num : ∀ n (a : Cd) → Dec (a ≡ num n)
dec-num zero hz = yes refl
dec-num zero (hs a) = no (λ ())
dec-num zero (hl f) = no (λ ())
dec-num zero (hΩ () f)
dec-num (suc n) hz = no (λ ())
dec-num (suc n) (hs a) with dec-num n a
... | yes e = yes (cong hs e)
... | no ne = no (λ e → ne (cong pred e))
dec-num (suc n) (hl f) = no (λ ())
dec-num (suc n) (hΩ () f)

normalise : ∀ n {y} → num n ≡ y → num n ≡ y
normalise n {y} p with dec-num n y
... | yes e = sym e
... | no ne = ⊥-elim (ne (sym p))
normalise-constant : ∀ n {y} (p q : num n ≡ y) → normalise n p ≡ normalise n q
normalise-constant n {y} p q with dec-num n y
... | yes e = refl
... | no ne = ⊥-elim (ne (sym p))
normalise-canonical : ∀ n {y} (p : num n ≡ y) →
  trans (sym (normalise n refl)) (normalise n p) ≡ p
normalise-canonical n refl = trans-symˡ (normalise n refl)
point-uip : ∀ n {y} (p q : num n ≡ y) → p ≡ q
point-uip n p q = trans (sym (normalise-canonical n p))
  (trans (cong (trans (sym (normalise n refl))) (normalise-constant n p q))
    (normalise-canonical n q))

SelfCase : ∀ n {t} → t ⊲ num (suc n) → Set
SelfCase n {t} p = Σ (t ≡ num (suc n)) (λ e →
  p ≡ subst (λ a → a ⊲ num (suc n)) (sym e) hself)
unroll : ∀ n {t} (p : t ⊲ num (suc n)) →
  SelfCase n p ⊎ Σ (t ⊲ num n) (λ r → p ≡ hsuc r)
unroll n hself = inj₁ (refl , refl)
unroll n (hsuc p) = inj₂ (p , refl)
self-canonical : ∀ n (e : num n ≡ num n) →
  subst (λ a → a ⊲ num n) (sym e) hself ≡ hself
self-canonical n e = cong (λ r → subst (λ a → a ⊲ num n) (sym r) hself)
  (point-uip n e refl)

path-unique : ∀ n {t} (p q : t ⊲ num n) → p ≡ q
path-unique zero hself hself = refl
path-unique (suc n) hself q with unroll n q
... | inj₁ (e , qe) = sym (trans qe (self-canonical (suc n) e))
... | inj₂ (r , qe) = ⊥-elim (¬s≤ᵛ (num n) (position-value r))
path-unique (suc n) (hsuc p) q with unroll n q
... | inj₁ (e , qe) = ⊥-elim (¬s≤ᵛ (num n)
  (position-value (subst (λ a → a ⊲ num n) e p)))
... | inj₂ (r , qe) = trans (cong hsuc (path-unique n p r)) (sym qe)

leg-num : ∀ n → leg (num n) ≡ num n
leg-num zero = refl
leg-num (suc n) = cong hs (leg-num n)

numF : ∀ n → F (num n) ≡ Finite.F n
numF zero = refl
numF (suc n) = cong step (numF n)
```

三个结论均量化全部n。path-unique使用右端这一具体有限树，而不是
从相同序数值识别两份路径；numF只沿step用类型等式，不使用函数
外延或任意KS结构的同值即相等。
