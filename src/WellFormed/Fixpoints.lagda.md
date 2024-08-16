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
ω^ : Func
ω^ a = 0 +ω^ a
```

```agda
+ω^-infl-rd : (_+ω^ b) inflates Road
+ω^-infl< : (_+ω^ b) inflates _<_
+ω^-infl< = ∣ +ω^-infl-rd ∣₁
```

```agda
+ω^-pres-rd : (a +ω^_) preserves Road
+ω^-pres< : (a +ω^_) preserves _<_
+ω^-pres< = map +ω^-pres-rd
```

```agda
a +ω^ zero = suc a
a +ω^ suc b = itω (_+ω^ b) a +ω^-infl<
a +ω^ lim f = lim (λ n → a +ω^ f n) ⦃ +ω^-pres< it ⦄
```

```agda
+ω^-infl-rd {(zero)} = zero
+ω^-infl-rd {suc b} = rd[ 1 ] +ω^-infl-rd
+ω^-infl-rd {lim f} = rd[ 0 ] +ω^-infl-rd
```

```agda
+ω^-pres-rd zero        = rd[ 2 ] +ω^-infl-rd
+ω^-pres-rd (suc r)     = rd[ 1 ] $ +ω^-pres-rd r
+ω^-pres-rd (lim {n} r) = rd[ n ] $ +ω^-pres-rd r
```

```agda
module _ (F : Func) (pres : F preserves _<_) ⦃ nz : NonZero (F 0) ⦄ where
  instance _ : NonZero (F (suc a))
  _ = nz-intro $                      begin-strict
    0                                 ≤⟨ z≤ ⟩
    F _                               <⟨ pres zero₁ ⟩
    F (suc _)                         ∎ where open SubTreeReasoning
```

```agda
  fixpt : Func
  fixpt-pres-rd : fixpt preserves Road
  fixpt-pres< : fixpt preserves _<_
  fixpt-pres< = map fixpt-pres-rd
```

```agda
  fixpt zero = itω F 0 w where
    w : wf (itn F 0)
    w {(zero)} = nz-elim
    w {suc n} = pres w
  fixpt (suc a) = let b = suc (fixpt a) in b + F b
  fixpt (lim f) = lim (λ n → fixpt (f n)) ⦃ fixpt-pres< it ⦄
```

```agda
  fixpt-pres-rd {x} zero =            begin-strict
    fixpt x                           <⟨ zero ⟩
    suc (fixpt x)                     <⟨ set +-infl< ⟩
    suc (fixpt x) + F (suc (fixpt x)) ∎ where open RoadReasoning
  fixpt-pres-rd {x} (suc {b} r) =     begin-strict
    fixpt x                           <⟨ fixpt-pres-rd r ⟩
    fixpt b                           <⟨ zero ⟩
    suc (fixpt b)                     <⟨ set +-infl< ⟩
    suc (fixpt b) + F (suc (fixpt b)) ∎ where open RoadReasoning
  fixpt-pres-rd {x} (lim {f} {n} r) = begin-strict
    fixpt x                           <⟨ fixpt-pres-rd r ⟩
    fixpt (f n)                       <⟨ f<l-rd ⟩
    lim (λ n → fixpt (f n)) ⦃ _ ⦄     ∎ where open RoadReasoning
```

```agda
ε : Func
ε = fixpt ω^ +ω^-pres<
```
