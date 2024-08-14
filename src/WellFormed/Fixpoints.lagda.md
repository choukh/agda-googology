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
