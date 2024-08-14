```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
open import Lower using (_∘ⁿ_)
itn : Func → Ord → Seq
itn F i n = (F ∘ⁿ n) i
```

```agda
itω : (F : Func) (i : Ord) (w : wf (itn F i)) → Ord
itω F i w = lim (itn F i) ⦃ w ⦄
```

```agda
_+ω^_ : Ord → Ord → Ord
+ω^-infl-rd : (_+ω^ b) inflates Road
+ω^-pres-rd : (a +ω^_) preserves Road

+ω^-infl< : (_+ω^ b) inflates _<_
+ω^-infl< = ∣ +ω^-infl-rd ∣₁

+ω^-pres< : (a +ω^_) preserves _<_
+ω^-pres< = map +ω^-pres-rd

a +ω^ zero = suc a
a +ω^ suc b = itω (_+ω^ b) a +ω^-infl<
a +ω^ lim f = lim (λ n → a +ω^ (f n)) ⦃ +ω^-pres< it ⦄

+ω^-infl-rd {(zero)} = zero
+ω^-infl-rd {suc b} = f<l-rd {n = 0} ⦃ _ ⦄
+ω^-infl-rd {lim f} = lim {n = 0} ⦃ _ ⦄ +ω^-infl-rd

+ω^-pres-rd zero        = lim {n = 2} ⦃ _ ⦄ +ω^-infl-rd
+ω^-pres-rd (suc r)     = lim {n = 1} ⦃ _ ⦄ (+ω^-pres-rd r)
+ω^-pres-rd (lim {n} r) = lim {n = n} ⦃ _ ⦄ (+ω^-pres-rd r)
```

```agda
ω^_ : Func
ω^ a = 0 +ω^ a
```

```agda
ε₀ : Ord
ε₀ = itω ω^_ 0 w where
  w : wf (itn ω^_ 0)
  w {(zero)} = zero₁
  w {suc n} = +ω^-pres< (w {n})
```

```agda
ε₁ : Ord
ε₁ = itω ω^_ (suc ε₀) w where
  open SubTreeReasoning
  v =                 begin-strict
    ε₀ +ω^ 0          <⟨ +ω^-pres< (z<l ⦃ _ ⦄) ⟩
    ε₀ +ω^ ε₀         ≈⟨ cong (_+ω^ ε₀) {!   !} ⟩
    (ω^ ε₀) +ω^ ε₀    ∎
  w : wf (itn ω^_ (suc ε₀))
  w {(zero)} =        begin-strict
    suc ε₀            ≈⟨ refl ⟩
    ε₀ +ω^ 0          <⟨ map (lim {n = 2} ⦃ _ ⦄) v ⟩
    itω (_+ω^ ε₀) 0 _ ≈⟨ refl ⟩
    ω^ (suc ε₀)       ∎
  w {suc n} = +ω^-pres< (w {n})
```
