```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
nonSuc : Ord → Type
nonSuc (suc a) = ⊥
nonSuc _ = ⊤

record NonSuc (a : Ord) : Type where
  field .wrap : nonSuc a
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
  fp : Bool
```

```agda
_+ω^⟨_⟩_ : Ord → Bool → Ord → Ord

ω^⟨_⟩_ : Bool → Ord → Ord
ω^⟨ fp ⟩ a = 0 +ω^⟨ fp ⟩ a

_+ω^_ : Ord → Ord → Ord
i +ω^ a = i +ω^⟨ false ⟩ a

ω^ : Func
ω^ = 0 +ω^_
```

```agda
ω^-infl-rd : Road i (i +ω^⟨ fp ⟩ a)
ω^-infl< : i < i +ω^⟨ fp ⟩ a
ω^-infl< = ∣ ω^-infl-rd ∣₁
```

```agda
ω^-pres-rd : Road a b → Road (i +ω^ a) (i +ω^ b)
ω^-pres< : a < b → i +ω^ a < i +ω^ b
ω^-pres< = map ω^-pres-rd
```

```agda
i         +ω^⟨ _     ⟩ zero = suc i
i         +ω^⟨ fp   ⟩ suc a = itω (_+ω^⟨ fp ⟩ a) i ω^-infl<
i         +ω^⟨ false ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(suc _) +ω^⟨ true  ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
i@(lim _) +ω^⟨ true  ⟩ lim f = lim (λ n → i +ω^ f n) ⦃ ω^-pres< it ⦄
zero      +ω^⟨ true  ⟩ lim f = lim f
```

```agda
ω^-infl-rd                            {a = zero}  = zero
ω^-infl-rd                            {a = suc a} = lim# 1 ω^-infl-rd
ω^-infl-rd              {fp = false} {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = suc _}  {fp = true}  {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = lim _}  {fp = true}  {a = lim f} = lim# 0 ω^-infl-rd
ω^-infl-rd {i = zero}   {fp = true}  {a = lim f} = z<l-rd
```

```agda
ω^-pres-rd zero         = lim# 2 ω^-infl-rd
ω^-pres-rd (suc r)      = lim# 1 (ω^-pres-rd r)
ω^-pres-rd (lim {n} r)  = lim# n (ω^-pres-rd r)
```

```agda
ω^-fp-pres-rd : ⦃ NonSuc a ⦄ → Road a b → Road (ω^⟨ true ⟩ a) (ω^⟨ true ⟩ b)
ω^-fp-pres< : ⦃ NonSuc a ⦄ → a < b → ω^⟨ true ⟩ a < ω^⟨ true ⟩ b
ω^-fp-pres< = map ω^-fp-pres-rd

ω^-fp-pres-rd             zero            = lim# 2 ω^-infl-rd
ω^-fp-pres-rd             (suc r)         = lim# 1 (ω^-fp-pres-rd r)
ω^-fp-pres-rd {a = zero}  (lim {f} {n} r) = lim# (suc n) $ begin-strict
  suc zero                      <⟨ s<s-rd r ⟩
  suc (f n)                     ≤⟨ <→s≤-rd (set it) ⟩
  f (suc n)                     ∎ where open RoadReasoning
ω^-fp-pres-rd {a = lim f} (lim {n} r) = lim# n r
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
ε₀-fp : ω^⟨ true ⟩ ε₀ ≡ ε₀
ε₀-fp = limExt λ _ → refl
```

```agda
ε₁ : Ord
ε₁ = lim h ⦃ h-wf ⦄ where
  h : Seq
  h zero = suc ε₀
  h (suc n) = ω^⟨ true ⟩ h n

  instance
    h-ns : NonSuc (h n)
    h-ns {(zero)} = {!   !}
    h-ns {suc n} = {!   !}

  open SubTreeReasoning

  h-wf-0-pre =                  begin-strict
    ε₀ +ω^ 0                    <⟨ ω^-pres< zero₁ ⟩
    ε₀ +ω^ 1                    ∎

  h-wf-0 =                      begin-strict
    ε₀ +ω^ 0                    <⟨ map (lim# 1) h-wf-0-pre ⟩
    ε₀ +ω^⟨ true ⟩ ε₀           ≈˘⟨ cong (_+ω^⟨ true ⟩ ε₀) ε₀-fp ⟩
    (ω^⟨ _ ⟩ ε₀) +ω^⟨ _ ⟩ ε₀    ∎

  h-wf : wf h
  h-wf {(zero)} = begin-strict
    suc ε₀                      ≈⟨ refl ⟩
    ε₀ +ω^ 0                    <⟨ map (lim# 2) h-wf-0 ⟩
    itω (_+ω^⟨ true ⟩ ε₀) 0 _   ≈⟨ refl ⟩
    ω^⟨ true ⟩ suc ε₀           ∎
  h-wf {suc zero} = {!   !}
  h-wf {2+ n} = {!   !}
```
ω^-fp-pres< (h-wf {n})
