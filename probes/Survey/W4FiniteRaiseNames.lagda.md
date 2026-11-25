# 同时提升原标准项的所有正有限下标

第四层。保持零下标，把每个正有限下标 j 换成 j+1。此变换严格保序，保持标准形、可数性以及有限下标证书，作用于任意正层的两次塌缩时恰得到下一层的两次塌缩。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseNames where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.EboLeanDef using (T; PT; 𝟏; ψ; natT; _<ᵀ_; _<ᴾ_; []<; hd<; ar<; lv<; tl<)
open import OCF.Align.EboLeanBase
import Survey.EboPTOFinite as B

index : T → T
index [] = []
index (x ∷ xs) = 𝟏 ∷ x ∷ xs

raise : T → T
letter : PT → PT
raise [] = []
raise (x ∷ ts) = letter x ∷ raise ts
letter (ψ u a) = ψ (index u) (raise a)

index< : ∀ {a b} → a <ᵀ b → index a <ᵀ index b
index< []< = []<
index< {a = _ ∷ _} {b = _ ∷ _} h = tl< h

reflect≤ : ∀ a b → index a ≤ᵀ index b → a ≤ᵀ b
reflect≤ a b h with tri a b
... | inj₁ d = inj₁ d
... | inj₂ (inj₁ e) = inj₂ e
... | inj₂ (inj₂ d) = ⊥-elim (<ᵀ-irrefl (<-≤ (index< d) h))

strict : ∀ {a b} → a <ᵀ b → raise a <ᵀ raise b
principal : ∀ {x y} → x <ᴾ y → letter x <ᴾ letter y
strict []< = []<
strict (hd< h) = hd< (principal h)
strict (tl< {x = ψ u a} h) = tl< (strict h)
principal (lv< h) = lv< (index< h)
principal (ar< h) = ar< (strict h)

sorted : ∀ x t → HdLe x t → HdLe (letter x) (raise t)
sorted x [] h = tt
sorted x (ψ u a ∷ t) (inj₁ d) = inj₁ (principal d)
sorted .(ψ u a) (ψ u a ∷ t) (inj₂ refl) = inj₂ refl

next : ℕ → ℕ
next zero = zero
next (suc n) = suc (suc n)

numeral : ∀ j → index (natT j) ≡ natT (next j)
numeral zero = refl
numeral (suc j) = refl

budget : ∀ {n t} → B.Indices n t → B.Indices (suc n) (raise t)
budget B.empty = B.empty
budget (B.cons {j = zero} _ a ts) = B.cons z≤n (budget a) (budget ts)
budget (B.cons {j = suc j} d a ts) = B.cons (s≤s d) (budget a) (budget ts)

count : ∀ {t} → Ctbl t → Ctbl (raise t)
count c[] = c[]
count (c∷ c) = c∷ (count c)

-- 新下标比原来的正自然数多一个 1；两者对零层能增加的支撑都只有空项。
index-support : ∀ u j {z} → InG (index u) z (index (natT j)) →
  Σ T (λ a → InG u a (natT j) × (z ≡ raise a))
index-support u zero ()
index-support [] (suc j) g = [] , gp (gh (inj₂ refl)) , B.num-support (suc (suc j)) g
index-support (_ ∷ _) (suc j) g = ⊥-elim (noG∷ (B.nf-num (suc (suc j))) []< g)

support : ∀ {n t z} u → B.Indices n t → InG (index u) z (raise t) →
  Σ T (λ a → InG u a t × (z ≡ raise a))
support u B.empty ()
support u (B.cons {j} _ a ts) (gp (gh e)) = _ , gp (gh (reflect≤ u (natT j) e)) , refl
support u (B.cons {j} _ a ts) (gp (gw e g)) with index-support u j g
... | b , h , eq = b , gp (gw (reflect≤ u (natT j) e) h) , eq
support u (B.cons {j} _ a ts) (gp (gc e g)) with support u a g
... | b , h , eq = b , gp (gc (reflect≤ u (natT j) e) h) , eq
support u (B.cons _ a ts) (gtl g) with support u ts g
... | b , h , eq = b , gtl h , eq

guard : ∀ {n t} u → B.Indices n t → GB u t t → GB (index u) (raise t) (raise t)
guard u a good h with support u a h
... | _ , old , refl = strict (good old)

normal : ∀ {n t} → B.Indices n t → NF t → NF (raise t)
normal B.empty n[] = n[]
normal (B.cons {j} _ a ts) (n∷ (nψ _ na g) h nt) = n∷
  (nψ (subst NF (sym (numeral j)) (B.nf-num (next j))) (normal a na) (guard (natT j) a g))
  (sorted _ _ h) (normal ts nt)

tower : ∀ n k → raise (B.tower (suc n) k) ≡ B.tower (suc (suc n)) k
tower n zero = refl
tower n (suc k) = cong (λ t → ψ (natT (suc (suc n))) t ∷ []) (tower n k)

target : ∀ n → raise (B.collapsed (suc n) 2) ≡ B.collapsed (suc (suc n)) 2
target n = cong (λ t → ψ [] t ∷ []) (tower n 2)
```
