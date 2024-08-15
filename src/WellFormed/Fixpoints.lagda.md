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
ω^-infl-rd : (a : Ord) (mdh : Maybe (DoHomo a)) → Road i (i +ω^⟨ a , mdh ⟩)
ω^-infl< : (a : Ord) (mdh : Maybe (DoHomo a)) → i < i +ω^⟨ a , mdh ⟩
ω^-infl< a mdh = ∣ ω^-infl-rd a mdh ∣₁
```

```agda
ω^-pres-rd : Road a b → Road (i +ω^ a) (i +ω^ b)
ω^-pres< : a < b → i +ω^ a < i +ω^ b
ω^-pres< = map ω^-pres-rd
```

```agda
i         +ω^⟨ zero  , nothing ⟩ = suc i
i         +ω^⟨ suc a , mdh     ⟩ = itω _+ω^⟨ a , mdh ⟩ i (ω^-infl< a mdh)
i         +ω^⟨ lim f , nothing ⟩ = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(suc _) +ω^⟨ lim f , just r  ⟩ = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(lim _) +ω^⟨ lim f , just r  ⟩ = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
zero      +ω^⟨ lim f , just r  ⟩ = lim h ⦃ h-wf ⦄
  module BaseOmega where
  h : Seq
  h zero = f 0
  h (suc n) = ω^ (f n)
  h-wf : wf h
  h-wf {(zero)} = r
  h-wf {suc n} = ω^-pres< it
```

```agda
ω^-infl-rd           zero    nothing   = zero
ω^-infl-rd           (suc a) mdh        = f<l-rd {n = 0} ⦃ _ ⦄
ω^-infl-rd           (lim f) nothing   = lim {n = 0} ⦃ _ ⦄ (ω^-infl-rd (f 0) nothing)
ω^-infl-rd {suc _}   (lim f) (just r)  = lim {n = 0} ⦃ _ ⦄ (ω^-infl-rd (f 0) nothing)
ω^-infl-rd {lim _}   (lim f) (just r)  = lim {n = 0} ⦃ _ ⦄ (ω^-infl-rd (f 0) nothing)
ω^-infl-rd {(zero)}  (lim f) (just r)  = lim {n = 1} ⦃ _ ⦄ (ω^-infl-rd (f 0) nothing)
```

```agda
ω^-pres-rd zero = lim {n = 2} ⦃ _ ⦄ (ω^-infl-rd _ nothing)
ω^-pres-rd (suc r) = lim {n = 1} ⦃ _ ⦄ (ω^-pres-rd r)
ω^-pres-rd (lim {n} r) = lim {n = n} ⦃ _ ⦄ (ω^-pres-rd r)
```

```agda
ω^-dh-pres-rd : {dha : DoHomo a} {dhb : DoHomo b} → Road a b → Road (i +ω^⟨ a , just dha ⟩) (i +ω^⟨ b , just dhb ⟩)
ω^-dh-pres< : {dha : DoHomo a} {dhb : DoHomo b} → a < b → i +ω^⟨ a , just dha ⟩ < i +ω^⟨ b , just dhb ⟩
ω^-dh-pres< = map ω^-dh-pres-rd

ω^-dh-pres-rd zero = lim {n = 2} ⦃ _ ⦄ {!   !}
ω^-dh-pres-rd (suc r) = {!   !}
ω^-dh-pres-rd (lim r) = {!   !}
```

```agda
ω⋰⟨_,_⟩ : (i : Ord) (w : wf (itn ω^ i)) → Ord
ω⋰⟨_,_⟩ = itω ω^
```

```agda
ε₀ : Ord
ε₀ = ω⋰⟨ 0 , w ⟩ where
  w : wf (itn ω^ 0)
  w {(zero)} = zero₁
  w {suc n} = ω^-pres< (w {n})
```

```agda
ε₀-fp : ω^⟨ ε₀ , just zero₁ ⟩ ≡ ε₀
ε₀-fp = limExt ⦃ _ ⦄ ⦃ _ ⦄ λ { zero → refl ; (suc n) → refl }
```

```agda
ε₁ : Ord
ε₁ = lim h ⦃ h-wf ⦄ where
  h : Seq
  hh : DoHomo (h n)

  h zero = suc ε₀
  h (suc n) = ω^⟨ h n , just hh ⟩

  hh {n} with (h n) in eq
  ...         | zero = {!   !}
  hh {(zero)} | suc a = case suc-inj eq of λ { refl → zero₁ }
  hh {suc n}  | suc a = {!   !}
  hh {suc n}  | lim f = {!   !}

  open SubTreeReasoning

  h-wf-0-pre =                  begin-strict
    ε₀ +ω^ 0                    <⟨ ω^-pres< zero₁ ⟩
    ε₀ +ω^ 1                    ∎

  h-wf-0 =                      begin-strict
    ε₀ +ω^ 0                    <⟨ map (lim {n = 1} ⦃ _ ⦄) h-wf-0-pre ⟩
    ε₀ +ω^⟨ ε₀ , _ ⟩            ≈˘⟨ cong (_+ω^⟨ ε₀ , just zero₁ ⟩) ε₀-fp ⟩
    ω^⟨ ε₀ , _ ⟩ +ω^⟨ ε₀ , _ ⟩  ∎

  h-wf : wf h
  h-wf {(zero)} =               begin-strict
    suc ε₀                      ≈⟨ refl ⟩
    ε₀ +ω^ 0                    <⟨ map (lim {n = 2} ⦃ _ ⦄) h-wf-0 ⟩
    itω _+ω^⟨ ε₀ , _ ⟩ 0 _      ≈⟨ refl ⟩
    ω^⟨ suc ε₀ , _ ⟩            ∎
  h-wf {suc n} = ω^-dh-pres< (h-wf {n})
```
