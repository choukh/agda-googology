# 换基地板与读回证据
候选，不替换主线；`split` 只沿目标路径给出地板上下的路径，不比较孩子。
`rbO` 对规范读回层号、`rb-tw` 对塔各项给出证据；`seen` 重建换基后的 Ω 树。
来源：Review18 的 seen 形状与 YiRBSib 的可缺证据组织；不是任意原树的换基。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRBSib as R

downOk : (ℓ : L) → Ok ℓ → (j : L) → j ≤ ℓ → Ok j
downOk ℓ o .ℓ self = o
downOk (nd s h) o j (inc c v) = downOk (h c) (proj₂ o c) j v
downOk (nd s h) o j (inu vs) = downOk (h (c₀ s)) (proj₂ o (c₀ s)) j (vs (c₀ s))
downOk (nd (sΩ k) h) o j (ink v) = downOk k (proj₁ (proj₁ o)) j v

raiseO : (a j b : L) → a ≤ j → OkO a b → OkO j b
raiseO a j zero u ob = tt
raiseO a j (nd sS h) u ob = tt , λ c → raiseO a j (h c) u (proj₂ ob c)
raiseO a j (nd sL h) u ob = proj₁ ob , λ c → raiseO a j (h c) u (proj₂ ob c)
raiseO a j (nd (sΩ k) h) u ob = (proj₁ (proj₁ ob) ∙ u , proj₂ (proj₁ ob)) , λ c → raiseO a j (h c) u (proj₂ ob c)

split : (a b : L) → OkO a b → ∀ {j} → j ≤ (a ⊕ b) → (j ≤ a) ⊎ (a ≤ j)
split a zero ob v = inj₁ v
split a (nd s h) ob self = inj₂ (lift a (nd s h))
split a (nd s h) ob (inc c v) = split a (h c) (proj₂ ob c) v
split a (nd s h) ob (inu vs) = split a (h (c₀ s)) (proj₂ ob (c₀ s)) (vs (c₀ s))
split a (nd (sΩ k) h) ob (ink v) = inj₁ (v ∙ proj₁ (proj₁ ob))

record Schema (k : L) (h : Tr k → L) : Set where
  constructor schema
  field
    floor : L
    offsets : Tr k → L
    ok-floor : Ok floor
    index-floor : k ≤ floor
    ok-offsets : (c : Tr k) → OkO floor (offsets c)
    shape : (c : Tr k) → h c ≡ floor ⊕ offsets c
open Schema public

RbS : (s : Sh) → (Ch s → L) → Set
RbS sS h = ⊤
RbS sL h = ⊤
RbS (sΩ k) h = Maybe (Schema k h)
Rb : L → Set
Rb zero = ⊤
Rb (nd s h) = RbS s h × ((c : Ch s) → Rb (h c))
rbS-no : (s : Sh) (h : Ch s → L) → RbS s h
rbS-no sS h = tt
rbS-no sL h = tt
rbS-no (sΩ k) h = nothing
rb-no : (ℓ : L) → Rb ℓ
rb-no zero = tt
rb-no (nd s h) = rbS-no s h , λ c → rb-no (h c)
rbO : (a b : L) → Rb a → Ok a → OkO a b → Rb (a ⊕ b)
rbO a zero ra oa ob = ra
rbO a (nd sS h) ra oa ob = tt , λ c → rbO a (h c) ra oa (proj₂ ob c)
rbO a (nd sL h) ra oa ob = tt , λ c → rbO a (h c) ra oa (proj₂ ob c)
rbO a (nd (sΩ k) h) ra oa ob =
  just (schema a h oa (proj₁ (proj₁ ob)) (proj₂ ob) (λ c → refl)) , λ c → rbO a (h c) ra oa (proj₂ ob c)
rb-tw : (n : ℕ) → Rb (tw n)
rb-tw zero = tt
rb-tw (suc n) = just (schema (tw n) (↑ (tw n)) (Ok-tw n) self (OkO↑ (tw n) (tw n) (Ok-tw n) self) (λ c → refl)) ,
  λ c → rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

seen : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j
seen S j oj u β c = R.ψ (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))

seen-step : ∀ {k h} (S : Schema k h) j oj u β c → j ⊢ proj₁ β ◃ proj₁ (seen S j oj u β c)
seen-step S j oj u β c = R.mono (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (proj₂ (Ωt (j ⊕ offsets S c)))

route : ∀ {k h} (S : Schema k h) j c′ → j ≤ h c′ → (j ≤ floor S) ⊎ (floor S ≤ j)
route S j c′ v = split (floor S) (offsets S c′) (ok-offsets S c′)
  (subst (λ b → j ≤ b) (shape S c′) v)
back : ∀ {k h j} (S : Schema k h) c → j ≤ floor S → j ≤ h c
back {j = j} S c u = subst (λ b → j ≤ b) (sym (shape S c)) (u ∙ lift (floor S) (offsets S c))
```
