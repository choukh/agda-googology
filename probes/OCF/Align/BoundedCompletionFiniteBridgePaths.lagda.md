# 有限终点的路径唯一性

只对字面自然数树终点消去路径差异；任意公共界B中的组件路径仍可不同。
证明不比较函数，不假定一般Cd路径证明无关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteBridgePaths where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)

position-value : ∀ {a b : Cd} → a ⊲ b → a ≤ᵛ b
position-value hself = ≤-refl _
position-value (hsuc p) = ≤s (position-value p)
position-value (hlim n p) = ≤l n (position-value p)

no-successor-back : ∀ (a : Cd) → hs a ⊲ a → ⊥
no-successor-back a p = ¬s≤ᵛ a (position-value p)

-- 固定有限终点的局部判等；不判定任意两棵Cd。
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (recompute; recompute-constant)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symʳ)

finite-equal? : ∀ n (a : Cd) → Dec (a ≡ num n)
finite-equal? zero hz = yes refl
finite-equal? zero (hs a) = no (λ ())
finite-equal? zero (hl f) = no (λ ())
finite-equal? (suc n) hz = no (λ ())
finite-equal? (suc n) (hs a) with finite-equal? n a
... | yes p = yes (cong hs p)
... | no p = no (λ { refl → p refl })
finite-equal? (suc n) (hl f) = no (λ ())

normal : ∀ n {a} → a ≡ num n → a ≡ num n
normal n {a} p = recompute (finite-equal? n a) p
normal-constant : ∀ n {a} (p q : a ≡ num n) → normal n p ≡ normal n q
normal-constant n {a} = recompute-constant (finite-equal? n a)
normal-canonical : ∀ n {a} (p : a ≡ num n) →
  trans (normal n p) (sym (normal n refl)) ≡ p
normal-canonical n refl = trans-symʳ (normal n refl)
local-UIP : ∀ n {a} (p q : a ≡ num n) → p ≡ q
local-UIP n p q = trans (sym (normal-canonical n p))
  (trans (cong (λ r → trans r (sym (normal n refl))) (normal-constant n p q))
    (normal-canonical n q))

Code : ℕ → Cd → Set
Code zero a = a ≡ hz
Code (suc n) a = (a ≡ hs (num n)) ⊎ Code n a
encode : ∀ n {a} → a ⊲ num n → Code n a
encode zero hself = refl
encode (suc n) hself = inj₁ refl
encode (suc n) (hsuc p) = inj₂ (encode n p)
decode : ∀ n {a} → Code n a → a ⊲ num n
decode zero refl = hself
decode (suc n) (inj₁ refl) = hself
decode (suc n) (inj₂ p) = hsuc (decode n p)
round : ∀ n {a} (p : a ⊲ num n) → decode n (encode n p) ≡ p
round zero hself = refl
round (suc n) hself = refl
round (suc n) (hsuc p) = cong hsuc (round n p)
code-unique : ∀ n {a} (p q : Code n a) → p ≡ q
code-unique zero p q = local-UIP zero p q
code-unique (suc n) (inj₁ p) (inj₁ q) = cong inj₁ (local-UIP (suc n) p q)
code-unique (suc n) (inj₁ p) (inj₂ q) = ⊥-elim
  (no-successor-back (num n) (subst (λ x → x ⊲ num n) p (decode n q)))
code-unique (suc n) (inj₂ p) (inj₁ q) = ⊥-elim
  (no-successor-back (num n) (subst (λ x → x ⊲ num n) q (decode n p)))
code-unique (suc n) (inj₂ p) (inj₂ q) = cong inj₂ (code-unique n p q)

finite-path-unique : ∀ n {a : Cd} (p q : a ⊲ num n) → p ≡ q
finite-path-unique n p q = trans (sym (round n p))
  (trans (cong (decode n) (code-unique n (encode n p) (encode n q))) (round n q))

finite-antisym : ∀ n {a : Cd} → a ⊲ num n → num n ⊲ a → a ≡ num n
finite-antisym zero hself q = refl
finite-antisym (suc n) hself q = refl
finite-antisym (suc n) (hsuc p) q =
  ⊥-elim (no-successor-back (num n) (⊲ᴮ-tr q p))
```

唯一性定理甚至允许起点a未预先写成自然数；终点num n是关键条件。
它不推出 a⊲B 的证明唯一，也不推出整个Path函数相等。
