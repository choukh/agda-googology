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
open import Cubical.Data.Maybe using (Maybe; nothing; just)
private variable i : Ord
```

```agda
DoHomo : Ord → Type
_+ω^⟨_,_⟩ : (i a : Ord) (mdh : Maybe (DoHomo a)) → Ord
```

```agda
ω^⟨_,_⟩ : (a : Ord) (mdh : Maybe (DoHomo a)) → Ord
ω^⟨ a , mdh ⟩ = 0 +ω^⟨ a , mdh ⟩

_+ω^_ : Ord → Ord → Ord
i +ω^ a = i +ω^⟨ a , nothing ⟩

ω^ : Func
ω^ = 0 +ω^_
```

```agda
DoHomo zero = ⊥
DoHomo (suc a) = DoHomo a
DoHomo (lim f) = f 0 < ω^ (f 0)
```

```agda
+ω^-infl-rd : (a : Ord) (mdh : Maybe (DoHomo a)) → Road i (i +ω^⟨ a , mdh ⟩)
+ω^-infl< : (a : Ord) (mdh : Maybe (DoHomo a)) → i < i +ω^⟨ a , mdh ⟩
+ω^-infl< a mdh = ∣ +ω^-infl-rd a mdh ∣₁
```

```agda
+ω^-pres-rd : Road a b → Road (i +ω^ a) (i +ω^ b)
+ω^-pres< : a < b → i +ω^ a < i +ω^ b
+ω^-pres< = map +ω^-pres-rd
```

```agda
i         +ω^⟨ zero  , nothing ⟩ = suc i
i         +ω^⟨ suc a , mdh     ⟩ = itω _+ω^⟨ a , mdh ⟩ i (+ω^-infl< a mdh)
i         +ω^⟨ lim f , nothing ⟩ = lim (λ n → i +ω^ f n) ⦃ +ω^-pres< it ⦄
i@(suc _) +ω^⟨ lim f , just r  ⟩ = lim (λ n → i +ω^ f n) ⦃ +ω^-pres< it ⦄
i@(lim _) +ω^⟨ lim f , just r  ⟩ = lim (λ n → i +ω^ f n) ⦃ +ω^-pres< it ⦄
zero      +ω^⟨ lim f , just r  ⟩ = lim h ⦃ h-wf ⦄
  module BaseOmega where
  h : Seq
  h zero = f 0
  h (suc n) = ω^ (f n)
  h-wf : wf h
  h-wf {(zero)} = r
  h-wf {suc n} = +ω^-pres< it
```

```agda
+ω^-infl-rd           zero    nothing   = zero
+ω^-infl-rd           (suc a) mdh        = f<l-rd {n = 0} ⦃ _ ⦄
+ω^-infl-rd           (lim f) nothing   = lim {n = 0} ⦃ _ ⦄ (+ω^-infl-rd (f 0) nothing)
+ω^-infl-rd {suc _}   (lim f) (just r)  = lim {n = 0} ⦃ _ ⦄ (+ω^-infl-rd (f 0) nothing)
+ω^-infl-rd {lim _}   (lim f) (just r)  = lim {n = 0} ⦃ _ ⦄ (+ω^-infl-rd (f 0) nothing)
+ω^-infl-rd {(zero)}  (lim f) (just r)  = lim {n = 1} ⦃ _ ⦄ (+ω^-infl-rd (f 0) nothing)
```

```agda
+ω^-pres-rd zero = lim {n = 2} ⦃ _ ⦄ (+ω^-infl-rd _ nothing)
+ω^-pres-rd (suc r) = lim {n = 1} ⦃ _ ⦄ (+ω^-pres-rd r)
+ω^-pres-rd (lim {n} r) = lim {n = n} ⦃ _ ⦄ (+ω^-pres-rd r)
```

```agda
+ω^-pres-rd-dh : (dh : DoHomo a) → Road a b → Road (i +ω^⟨ a , just dh ⟩) (i +ω^ b)
+ω^-pres<-dh : (dh : DoHomo a) → a < b → i +ω^⟨ a , just dh ⟩ < i +ω^ b
+ω^-pres<-dh dh = map (+ω^-pres-rd-dh dh)

+ω^-pres-rd-dh dh zero = {!   !}
+ω^-pres-rd-dh dh (suc r) = {!   !}
+ω^-pres-rd-dh dh (lim r) = {!   !}
```

```agda
ω⋰⟨_,_⟩ : (i : Ord) (w : wf (itn ω^ i)) → Ord
ω⋰⟨_,_⟩ = itω ω^
```

```agda
IsLim : Ord → Type
IsLim zero = ⊥
IsLim (suc a) = ⊥
IsLim (lim f) = ⊤
```

```agda
ω⋰⁺⟨_,_⟩ : (i : Ord) ⦃ l : IsLim i ⦄ (dh : DoHomo i) → Ord
ω⋰⁺⟨ i@(lim f) , dh ⟩ = lim h ⦃ h-wf ⦄
  module Jump where
  h : Seq
  h zero = ω^⟨ suc i , just dh ⟩
  h (suc n) = ω^ (h n)
  h-wf : wf h
  h-wf {(zero)} = +ω^-pres<-dh {a = suc i} {b = h 0} dh {!   !}
  h-wf {suc n} = +ω^-pres< (h-wf {n})
```

```agda
ε₀ : Ord
ε₀ = ω⋰⟨ 0 , w ⟩ where
  w : wf (itn ω^ 0)
  w {(zero)} = zero₁
  w {suc n} = +ω^-pres< (w {n})
```

```agda
ε₀-fp : ω^⟨ ε₀ , just zero₁ ⟩ ≡ ε₀
ε₀-fp = limExt ⦃ _ ⦄ ⦃ _ ⦄ λ { zero → refl ; (suc n) → refl }
```

```agda
ε₁ : Ord
ε₁ = ω⋰⁺⟨ ε₀ , zero₁ ⟩
```
