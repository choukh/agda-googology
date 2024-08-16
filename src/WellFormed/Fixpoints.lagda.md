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
data Jumpable (i : Ord) : Ord → Type where
  zero : Jumpable i i
  suc  : Jumpable i (suc a)

private variable i : Ord
instance
  jump-zero : Jumpable i i
  jump-zero = zero
  jump-suc : Jumpable i (suc a)
  jump-suc = suc

JumpableFunc : Ord → Type
JumpableFunc i = (a : Ord) ⦃ j : Jumpable i a ⦄ → Ord
```

```agda
module _ (i : Ord) (F : JumpableFunc i) ⦃ nz : ∀ {a} → NonZero (F (suc a)) ⦄ where
  jump : Func

  jump-pres-rd : jump preserves Road
  jump-pres< : jump preserves _<_
  jump-pres< = map jump-pres-rd
```

```agda
  jump zero = F i
  jump (suc a) = let b = suc (jump a) in b + F b
  jump (lim f) = lim (λ n → jump (f n)) ⦃ jump-pres< it ⦄
```

```agda
  jump-pres-rd {x} zero =             begin-strict
    jump x                            <⟨ zero ⟩
    suc (jump x)                      <⟨ set $ +-infl< ⟩
    suc (jump x) + F (suc (jump x))   ∎ where open RoadReasoning
  jump-pres-rd {x} (suc {b} r) =      begin-strict
    jump x                            <⟨ jump-pres-rd r ⟩
    jump b                            <⟨ zero ⟩
    suc (jump b)                      <⟨ set $ +-infl< ⟩
    suc (jump b) + F (suc (jump b))   ∎ where open RoadReasoning
  jump-pres-rd {x} (lim {f} {n} r) =  begin-strict
    jump x                            <⟨ jump-pres-rd r ⟩
    jump (f n)                        <⟨ f<l-rd {n = n} ⟩
    lim (λ n → jump (f n)) ⦃ _ ⦄      ∎ where open RoadReasoning
```

```agda
nonLim : Ord → Type
nonLim (lim _) = ⊥
nonLim _ = ⊤

record NonLim (a : Ord) : Type where
  field .wrap : nonLim a

instance
  zero-nl : NonLim zero
  zero-nl = _
  suc-nl : NonLim (suc a)
  suc-nl = _
```

```agda
fixpt : (F : Func)
  (infl : (F ↾ _) inflates _<_ within NonLim)
  (pres : F preserves _<_)
  → Func
fixpt F infl pres = jump 0 (λ x ⦃ j ⦄ → itω F x w) ⦃ _ ⦄ where
  w : ⦃ Jumpable 0 a ⦄ → wf (itn F a)
  w {a = zero} {n = zero} = infl
  w {a = suc a} {n = zero} = infl
  w {a = a} {n = suc n} = pres w
```

```agda
ε : Func
ε = fixpt ω^ w +ω^-pres< where
  w : (ω^ ↾ _) inflates _<_ within NonLim
  w {(zero)} = zero₁
  w {suc a} = {!   !}
```
