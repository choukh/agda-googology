# 第零塔对任意多次相同回灌的策略

第四层，无条件。对任意份 ψ₀(Ω₁) 接零下标尾项，一次压缩跳转恰消耗一份，任意长的普通前缀共用同一条定理。由此从 ψ₀(Ω₁+1) 出发的全部跳转可在实际第零塔执行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4CriticalStrategy where

open import Data.Nat.Base using (ℕ; zero; suc; z≤n)
open import Data.List.Base using ([]; _∷_; _++_; replicate)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.EboLeanDef hiding (lt; eq)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq)
import Survey.EboPTOFinite as F
open import Survey.W4CriticalDescent
open import Survey.W4MultisetDescent using (Place; visit; start; Step; follow)
import W4Fold as Fold
open import WVOne using (read)
import OCF.Align.Level as L

Low = F.Indices 0

without-last : ∀ t → Low (sucT t) → Low t
without-last [] p = F.empty
without-last (_ ∷ ts) (F.cons h a r) = F.cons h a (without-last ts r)

pred-low : ∀ t → cof t ≡ c1 → Low t → Low (pred t)
pred-low t e p = without-last (pred t) (subst Low (sym (pred-suc t e)) p)

repeat-low : ∀ {a} → Low a → ∀ n → Low (replicate n (ψ [] a))
repeat-low p zero = F.empty
repeat-low p (suc n) = F.cons z≤n p (repeat-low p n)

inside : ∀ {t} → Low t → (v : Vω t) → ∀ n → Low (fω v n)
inside (F.cons {j = suc _} () _ _)
inside (F.cons h a ts) (ws v) n = F.cons h a (inside ts v n)
inside (F.cons {j = zero} _ _ _) (wl () v) n
inside (F.cons {j = zero} _ a _) (w4 e) n = repeat-low (pred-low _ e a) n
inside (F.cons h a _) (w5 _ v) n = F.cons h (inside a v n) F.empty
inside (F.cons _ a _) (w6 _ _ v) n = ⊥-elim (no-omega a v)

tower-low : ∀ n → Low (pureTower n)
tower-low zero = F.cons z≤n F.empty F.empty
tower-low (suc n) = F.cons z≤n (tower-low n) F.empty

data Row : ℕ → T → Set where
  tail : ∀ {t} → Low t → Row 0 t
  more : ∀ {k t} → Row k t → Row (suc k) (epsilon ∷ t)

data Change : Kind → ℕ → ℕ → Set where
  stay : ∀ {k} → Change plain k k
  take : ∀ {k} → Change feedback (suc k) k

Result : Kind → ℕ → T → Set
Result c k s = Σ ℕ λ j → Change c k j × Row j s

prepend : ∀ {c k t} → Result c k t → Result c (suc k) (epsilon ∷ t)
prepend (_ , stay , r) = _ , stay , more r
prepend (_ , take , r) = _ , take , more r

empty-count : ∀ {k} → Row k [] → k ≡ 0
empty-count (tail _) = refl

at-limit : ∀ {t k} → Row k t → (e : cof t ≡ cω) → ∀ n →
  Result (kind (vω t e)) k (fsn t n)
at-limit {t} (tail p) e n rewrite quiet p (vω t e) =
  0 , stay , tail (subst Low (sym (fω-eq (vω t e) n)) (inside p (vω t e) n))
at-limit (more {t = []} r) refl n rewrite empty-count r =
  0 , take , tail (subst Low (sym (spent n)) (tower-low (suc n)))
at-limit (more {t = _ ∷ _} r) e n = prepend (at-limit r e n)

at-pred : ∀ {t k} → Row k t → cof t ≡ c1 → Row k (pred t)
at-pred (tail p) e = tail (pred-low _ e p)
at-pred (more {t = []} r) ()
at-pred (more {t = _ ∷ _} r) e = more (at-pred r e)

one-edge : ∀ {c k t s} → Row k t → Edge c t s → Result c k s
one-edge r (prev e) = _ , stay , at-pred r e
one-edge r (at e n) = at-limit r e n

jump : ∀ {t s k} → Row k t → Jump t s → Result feedback k s
jump r (fire e) = one-edge r e
jump r (skip e j) with one-edge r e
... | _ , stay , r′ = jump r′ j

batch : ∀ n → Row n (replicate n epsilon)
batch zero = tail F.empty
batch (suc n) = more (batch n)

top = ψ [] (sucT (Ωt (natT 1))) ∷ []

entry-shape : ∀ {c t s} → Edge c t s → t ≡ top →
  c ≡ plain × (Σ ℕ λ n → s ≡ replicate n epsilon)
entry-shape (prev e) refl with e
... | ()
entry-shape (at e n) refl = refl , n , copies-entry n

initial : ∀ {s} → Jump top s → Σ ℕ λ k → Row k s
initial (fire e) with entry-shape e refl
... | () , _
initial (skip e j) with entry-shape e refl
... | _ , n , refl with jump (batch n) j
...   | k , take , r = k , r

Y = read Fold.EBOᶜ

begin : ∀ {s} → Jump top s → Σ ℕ λ k → Row k s × Place Y (L.natᶜ k)
begin j with initial j
... | k , r = k , r , visit start (enter k)

advance : ∀ {t s k} → Row k t → (p : Place Y (L.natᶜ k)) → Jump t s →
  Σ ℕ λ i → Σ (Row i s) λ _ → Σ (Place Y (L.natᶜ i)) λ q →
    Step (L.natᶜ k , p) (L.natᶜ i , q)
advance r p j with jump r j
... | k , take , r′ = k , r′ , visit p (consume k) , follow (consume k)
```
