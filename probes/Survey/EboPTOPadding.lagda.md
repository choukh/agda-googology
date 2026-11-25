# 有限列上的带支撑塌缩

第四层，无条件。对降序和在末尾加一个主项，所得参数严格超过旧参数。若另一个目标已经盖住旧参数，且其每一项都严格大于本次加入的主项，则更新后仍严格低于目标。
把参数交给两层 Buchholz 塌缩时，这条律给出 Freund 比较所需的支撑条件。实际可用的层号是 2。[有限初段](EboPTOFinite.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.EboPTOPadding where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase
open import Survey.EboPTOFinite using (bottom; index<; nf-num; num-support)

data Push (k : PT) : T → T → Set where
  end  : Push k [] (k ∷ [])
  drop : ∀ {x xs} → x <ᴾ k → Push k (x ∷ xs) (k ∷ [])
  keep : ∀ {x xs ys} → k ≤ᴾ x → Push k xs ys → Push k (x ∷ xs) (x ∷ ys)

push : (k : PT) (p : T) → Σ T (Push k p)
push k [] = _ , end
push k (x ∷ xs) with tri (x ∷ []) (k ∷ [])
... | inj₁ (hd< h) = _ , drop h
... | inj₁ (tl< ())
... | inj₂ (inj₁ refl) = _ , keep (inj₂ refl) (proj₂ (push k xs))
... | inj₂ (inj₂ (hd< h)) = _ , keep (inj₁ h) (proj₂ (push k xs))
... | inj₂ (inj₂ (tl< ()))

rises : ∀ {k p q} → Push k p q → p <ᵀ q
rises end = []<
rises (drop e) = hd< e
rises (keep _ r) = tl< (rises r)

head-bound : ∀ {x k p q} → k ≤ᴾ x → HdLe x p → Push k p q → HdLe x q
head-bound v _ end = v
head-bound v _ (drop _) = v
head-bound _ h (keep _ _) = h

sorted : ∀ {k p q} → NFP k → NF p → Push k p q → NF q
sorted nk n[] end = n∷ nk tt n[]
sorted nk _ (drop _) = n∷ nk tt n[]
sorted nk (n∷ nx h nt) (keep v r) = n∷ nx (head-bound v h r) (sorted nk nt r)

support : ∀ {u z k p q} → Push k p q → InG u z q → InG u z p ⊎ InGP u z k
support end (gp g) = inj₂ g
support end (gtl ())
support (drop _) (gp g) = inj₂ g
support (drop _) (gtl ())
support (keep _ r) (gp g) = inj₁ (gp g)
support (keep _ r) (gtl g) with support r g
... | inj₁ v = inj₁ (gtl v)
... | inj₂ v = inj₂ v

data Floor (k : PT) : T → Set where
  nil : Floor k []
  more : ∀ {x xs} → k ≤ᴾ x → Floor k xs → Floor k (x ∷ xs)

floor : ∀ {k p q} → Push k p q → Floor k q
floor end = more (inj₂ refl) nil
floor (drop _) = more (inj₂ refl) nil
floor (keep h r) = more h (floor r)

p<≤ : ∀ {x y z} → x <ᴾ y → y ≤ᴾ z → x <ᴾ z
p<≤ h (inj₁ q) = <ᴾ-trans h q
p<≤ h (inj₂ refl) = h

below : ∀ {k l p p′ q} → Push k p p′ → Floor l q → k <ᴾ l → p <ᵀ q → p′ <ᵀ q
below end (more v _) h []< = hd< (p<≤ h v)
below (drop _) (more v _) h _ = hd< (p<≤ h v)
below (keep _ r) (more _ _) h (hd< v) = hd< v
below (keep _ r) (more _ f) h (tl< v) = tl< (below r f h v)

one = natT 1
two = natT 2
D₁ = ψ one
D₂ = ψ two
high = λ p → D₂ p ∷ []
out = λ p → ψ [] (high p) ∷ []

record Stage : Set where
  constructor stage
  field
    p : T
    normal : NF p
    low : p <ᵀ Ωt two
    guard : GB [] p (high p)
open Stage public

dark : ∀ {u a z} → NF a → a <ᵀ Ωt u → InG u z a → ⊥
dark n[] _ ()
dark n@(n∷ {x = ψ w b} _ _ _) h g = noG∷ n (index< h) g

low-high : ∀ {p q} → p <ᵀ Ωt two → p <ᵀ high q
low-high []< = []<
low-high (hd< (lv< h)) = hd< (lv< h)
low-high (hd< (ar< ()))
low-high (tl< ())

high< : ∀ {p q} → p <ᵀ q → high p <ᵀ high q
high< e = hd< (ar< e)

out< : ∀ {p q} → p <ᵀ q → out p <ᵀ out q
out< h = hd< (ar< (high< h))

out-normal : (s : Stage) → NF (out (p s))
out-normal s = nf-ψ n[] (nf-ψ (nf-num 2) (normal s) (λ g → ⊥-elim (dark (normal s) (low s) g))) check
  where
  check : GB [] (high (p s)) (high (p s))
  check (gp (gh _)) = low-high (low s)
  check (gp (gw _ g)) rewrite num-support 2 g = []<
  check (gp (gc _ g)) = guard s g
  check (gtl ())

emptyStage : Stage
emptyStage = stage [] n[] []< GB[]

extend : (s : Stage) (e : T) → NFP (D₁ e) →
  (∀ {q} → p s <ᵀ q → ∀ {z} → InGP [] z (D₁ e) → z <ᵀ high q) →
  Σ Stage λ t → Push (D₁ e) (p s) (p t)
extend s e ne bounded with push (D₁ e) (p s)
... | q , r = stage q (sorted ne (normal s) r) (below r (more (inj₂ refl) nil) (lv< (tl< []<)) (low s)) check , r
  where
  check : GB [] q (high q)
  check g with support r g
  ... | inj₁ old = <ᵀ-trans (guard s old) (high< (rises r))
  ... | inj₂ new = bounded (rises r) new
```
