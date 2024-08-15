```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
lim# : (n : ℕ) {w : wf f} → Road a (f n) → Road a (lim f ⦃ w ⦄)
lim# n = lim {n = n} ⦃ _ ⦄
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
open import Data.Bool using (Bool; true; false)
private variable
  i : Ord
  fix : Bool
```

```agda
_+ω^⟨_⟩_ : Ord → Bool → Ord → Ord

ω^⟨_⟩_ : Bool → Ord → Ord
ω^⟨ fix ⟩ a = 0 +ω^⟨ fix ⟩ a

_+ω^_ : Ord → Ord → Ord
i +ω^ a = i +ω^⟨ false ⟩ a

ω^ : Func
ω^ = 0 +ω^_
```

```agda
ω^-infl-rd : Road i (i +ω^⟨ fix ⟩ a)
ω^-infl< : i < i +ω^⟨ fix ⟩ a
ω^-infl< = ∣ ω^-infl-rd ∣₁
```

```agda
ω^-pres-rd : Road a b → Road (i +ω^ a) (i +ω^ b)
ω^-pres< : a < b → i +ω^ a < i +ω^ b
ω^-pres< = map ω^-pres-rd
```

```agda
i         +ω^⟨ _     ⟩ zero = suc i
i         +ω^⟨ fix   ⟩ suc a = itω (_+ω^⟨ fix ⟩ a) i ω^-infl<
i         +ω^⟨ false ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(suc _) +ω^⟨ true  ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(lim _) +ω^⟨ true  ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
zero      +ω^⟨ true  ⟩ lim f = lim f
```

```agda
ω^-infl-rd                            {a = zero}  = zero
ω^-infl-rd                            {a = suc a} = lim# 1 ω^-infl-rd
ω^-infl-rd              {fix = false} {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = suc _}  {fix = true}  {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = lim _}  {fix = true}  {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = zero}   {fix = true}  {a = lim f} = z<l-rd
```

```agda
ω^-pres-rd zero         = lim# 2 ω^-infl-rd
ω^-pres-rd (suc r)      = lim# 1 (ω^-pres-rd r)
ω^-pres-rd (lim {n} r)  = lim# n (ω^-pres-rd r)
```
